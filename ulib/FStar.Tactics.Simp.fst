(*
   Copyright 2025

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

(** Attribute-driven equational rewriting tactic for F*.

    Tag lemmas with [@@simp] for automatic discovery.
    Use [simp_tac()] in a [by (...)] block to rewrite the goal
    using all in-scope [@@simp] lemmas, bottom-up, to a fixed point.

    Architecture follows FStar.Tactics.Typeclasses:
    - Attribute-based lemma discovery via [lookup_attr_ses]
    - Head-symbol indexing for fast candidate lookup
    - [ctrl_rewrite BottomUp] with skip-based ctrl for efficiency
    - Fuel-bounded fixed-point iteration
*)
module FStar.Tactics.Simp

open FStar.Reflection.V2
open FStar.Reflection.V2.Formula
open FStar.Reflection.V2.Derived
open FStar.Stubs.Reflection.V2.Data
open FStar.Stubs.Tactics.Common
open FStar.Tactics.Effect
open FStar.Stubs.Tactics.V2.Builtins
open FStar.Stubs.Tactics.Types
open FStar.Tactics.V2.SyntaxHelpers
open FStar.Tactics.V2.Derived
open FStar.Tactics.V2.SyntaxCoercions
open FStar.Tactics.NamedView
open FStar.Tactics.Util

module L = FStar.List.Tot.Base
let (@) = L.op_At

(* ═══════════════════════════════════════════════
   Attribute
   ═══════════════════════════════════════════════ *)

(** Tag a lemma with [@@simp] for automatic discovery by [simp_tac]. *)
irreducible let simp : unit = ()

(* ═══════════════════════════════════════════════
   Types
   ═══════════════════════════════════════════════ *)

(** A parsed simp lemma ready for matching. *)
noeq
type simp_lemma = {
  sl_term  : term;        (* The lemma term, for apply_lemma_rw *)
  sl_head  : option name; (* Head fvar of LHS. None = unindexable / wildcard *)
  sl_cond  : bool;        (* True if the lemma has a non-trivial precondition *)
}

(** Head-symbol indexed association list. *)
type simp_index = list (name & list simp_lemma)

(** Internal state for one simp invocation. *)
noeq
type simp_state = {
  index     : simp_index;       (* Indexed lemmas: head fvar → candidates *)
  unindexed : list simp_lemma;  (* Wildcard-headed lemmas, always tried *)
  extras    : list simp_lemma;  (* Explicitly-passed extra lemmas *)
  changed   : tref bool;        (* Did any rewrite fire this round? *)
  fuel      : nat;              (* Max rounds remaining *)
  dbg       : bool;             (* Debug printing *)
}

(* ═══════════════════════════════════════════════
   Helpers — reused from Typeclasses patterns
   ═══════════════════════════════════════════════ *)

(** Extract the name of a sigelt. Handles Sg_Let and Sg_Val.
    Same logic as Typeclasses.sigelt_name. *)
private
let sigelt_name (se : sigelt) : Tac fv =
  match inspect_sigelt se with
  | Sg_Let {lbs} -> (
    match lbs with
    | [lb] -> lb.lb_fv
    | _ -> fail "simp: sigelt_name: multiple let bindings"
  )
  | Sg_Val {nm} -> pack_fv nm
  | _ -> fail "simp: sigelt_name: unsupported sigelt shape"

(** Extract the head fvar from a term by chasing Tv_App.
    Same logic as Typeclasses.head_of. *)
private
let rec head_of (t : term) : Tac (option fv) =
  match inspect t with
  | Tv_FVar fv
  | Tv_UInst fv _ -> Some fv
  | Tv_App h _ -> head_of h
  | _ -> None

(** Get the result type of an arrow chain. *)
private
let rec res_typ (t : term) : Tac term =
  match inspect t with
  | Tv_Arrow _ c -> (
    match inspect_comp c with
    | C_Total t -> res_typ t
    | _ -> t
  )
  | _ -> t

(** Compare fvar names. *)
private
let name_eq (n1 n2 : name) : Tot bool = n1 = n2

(** Backtracking combinator: try first, on any exception try second. *)
private
let ( >>> ) #a (t1 t2 : unit -> Tac a) () : Tac a =
  try t1 ()
  with | _ -> t2 ()

(* ═══════════════════════════════════════════════
   Lemma parsing
   ═══════════════════════════════════════════════ *)

(** Try to extract the type of a sigelt without calling tc.
    For Sg_Val we get the type directly. For Sg_Let we use lb_typ. *)
private
let sigelt_type (se : sigelt) : Tac (option term) =
  match inspect_sigelt se with
  | Sg_Val {typ} -> Some typ
  | Sg_Let {lbs} -> (
    match lbs with
    | [lb] -> Some lb.lb_typ
    | _ -> None
  )
  | _ -> None

(** Extract the LHS head symbol from a lemma conclusion.

    Given a type like [a1:t1 -> ... -> Lemma (lhs == rhs)],
    strips arrows, inspects the computation type, extracts the
    equality LHS, and returns its head fvar name. *)
private
let parse_lemma_type (typ : term) : Tac (option (option name & bool)) =
  (* Strip top-level arrows to reach the result comp *)
  let (bs, cod) = collect_arr_bs typ in
  match inspect_comp cod with
  | C_Lemma pre post _pats ->
    (* post is thunked: fun () -> body. Normalize to get body. *)
    let unit_tm = pack (Tv_Const C_Unit) in
    let post_body = norm_term [iota; zeta] (mk_e_app post [unit_tm]) in
    begin match term_as_formula' post_body with
    | Comp (Eq _) lhs _rhs ->
      let hd = head_of lhs in
      let hd_name = (match hd with | Some fv -> Some (inspect_fv fv) | None -> None) in
      (* Check precondition triviality *)
      let pre_body = norm_term [iota; primops; delta_qualifier ["unfold"]] pre in
      let is_cond = not (
        match term_as_formula' pre_body with
        | True_ -> true
        | _ -> false
      ) in
      Some (hd_name, is_cond)
    | _ -> None
    end
  | C_Total ret_typ ->
    (* Handle squash (lhs == rhs) shape *)
    begin match unsquash_term ret_typ with
    | Some inner ->
      begin match term_as_formula' inner with
      | Comp (Eq _) lhs _rhs ->
        let hd = head_of lhs in
        let hd_name = (match hd with | Some fv -> Some (inspect_fv fv) | None -> None) in
        Some (hd_name, false)
      | _ -> None
      end
    | None -> None
    end
  | _ -> None

(** Parse a sigelt into a simp_lemma. Returns None if not usable. *)
private
let parse_simp_sigelt (se : sigelt) : Tac (option simp_lemma) =
  try
    let fv = sigelt_name se in
    let tm = pack (Tv_FVar fv) in
    match sigelt_type se with
    | None -> None
    | Some typ ->
      begin match parse_lemma_type typ with
      | Some (hd_name, is_cond) ->
        Some { sl_term = tm; sl_head = hd_name; sl_cond = is_cond }
      | None ->
        (* Fallback: try tc to get a more precise type *)
        begin try
          let typ' = tc (cur_env ()) tm in
          match parse_lemma_type typ' with
          | Some (hd_name, is_cond) ->
            Some { sl_term = tm; sl_head = hd_name; sl_cond = is_cond }
          | None -> None
        with | _ -> None
        end
      end
  with | _ -> None

(** Parse an arbitrary term (not just an fv) into a simp_lemma. *)
private
let parse_simp_term (t : term) : Tac (option simp_lemma) =
  try
    let typ = tc (cur_env ()) t in
    match parse_lemma_type typ with
    | Some (hd_name, is_cond) ->
      Some { sl_term = t; sl_head = hd_name; sl_cond = is_cond }
    | None -> None
  with | _ -> None

(* ═══════════════════════════════════════════════
   Head-symbol index
   ═══════════════════════════════════════════════ *)

(** Insert a lemma into the index under its head symbol. *)
private
let rec index_insert (nm : name) (lem : simp_lemma) (idx : simp_index) : Tot simp_index =
  match idx with
  | [] -> [(nm, [lem])]
  | (k, vs) :: rest ->
    if name_eq k nm
    then (k, lem :: vs) :: rest
    else (k, vs) :: index_insert nm lem rest

(** Lookup candidates from index for a given head name. *)
private
let rec index_lookup (nm : name) (idx : simp_index) : Tot (list simp_lemma) =
  match idx with
  | [] -> []
  | (k, vs) :: rest ->
    if name_eq k nm then vs
    else index_lookup nm rest

(** Check if any entry exists for a head name. *)
private
let rec index_has (nm : name) (idx : simp_index) : Tot bool =
  match idx with
  | [] -> false
  | (k, _) :: rest ->
    if name_eq k nm then true
    else index_has nm rest

(** Build a simp_index from a list of parsed simp_lemmas.
    Unconditional lemmas are placed before conditional ones for priority. *)
private
let build_simp_index (lems : list simp_lemma) : Tot (simp_index & list simp_lemma) =
  (* Partition: unconditional first, then conditional *)
  let uncond = L.filter (fun lem -> not lem.sl_cond) lems in
  let cond = L.filter (fun lem -> lem.sl_cond) lems in
  let ordered = uncond @ cond in
  L.fold_left (fun (idx, unidx) lem ->
    match lem.sl_head with
    | Some nm -> (index_insert nm lem idx, unidx)
    | None    -> (idx, lem :: unidx)
  ) ([], []) ordered

(* ═══════════════════════════════════════════════
   Rewrite engine
   ═══════════════════════════════════════════════ *)

(** Get all candidate simp lemmas for a given subterm. *)
private
let get_candidates (st : simp_state) (t : term) : Tac (list simp_lemma) =
  let from_index =
    match head_of t with
    | Some fv -> index_lookup (inspect_fv fv) st.index
    | None -> []
  in
  from_index @ st.unindexed @ st.extras

(** The ctrl callback for ctrl_rewrite.
    Returns (false, Continue) for subterms with no matching head,
    avoiding the overhead of creating an equality goal. *)
private
let simp_ctrl (st : simp_state) (t : term) : Tac (bool & ctrl_flag) =
  match inspect t with
  | Tv_Uvar _ _ -> (false, Continue)
  | Tv_BVar _   -> (false, Continue)
  | Tv_Type _   -> (false, Continue)
  | _ ->
    let dominated =
      match head_of t with
      | Some fv -> index_has (inspect_fv fv) st.index
      | None -> false
    in
    let try_it = dominated
              || not (Nil? st.unindexed)
              || not (Nil? st.extras)
    in
    (try_it, Continue)

(** Try to apply a list of simp lemmas at the current rewrite position.
    On success, marks progress. On failure of all, uses trefl (no change). *)
private
let rec try_lemmas (lems : list simp_lemma) (changed : tref bool) : Tac unit =
  match lems with
  | [] -> trefl ()
  | lem :: rest ->
    (fun () ->
      apply_lemma_rw lem.sl_term;
      write changed true
    ) `or_else` (fun () ->
      try_lemmas rest changed
    )

(** The rw callback for ctrl_rewrite.
    Inspects the equality goal, extracts the LHS,
    looks up candidates, and tries each. *)
private
let simp_rw (st : simp_state) () : Tac unit =
  let g = cur_goal () in
  match term_as_formula g with
  | Comp (Eq _) lhs _rhs ->
    begin match inspect lhs with
    | Tv_Uvar _ _ -> trefl ()
    | _ ->
      let candidates = get_candidates st lhs in
      try_lemmas candidates st.changed
    end
  | _ -> trefl ()

(** One round of bottom-up rewriting. Returns true iff any rewrite fired. *)
private
let simp_round (st : simp_state) : Tac bool =
  write st.changed false;
  ctrl_rewrite BottomUp (simp_ctrl st) (simp_rw st);
  read st.changed

(** Main simp engine: iterate rewrite rounds until
    fixed-point or fuel exhaustion. *)
private
let rec simp_loop (st : simp_state) (fuel : nat) : Tac unit =
  if fuel = 0 then ()
  else begin
    let progress = simp_round st in
    if progress then begin
      (* Normalize between rounds to expose new redexes *)
      norm [iota; primops];
      simp_loop st (fuel - 1)
    end
    else ()
  end

(* ═══════════════════════════════════════════════
   State construction
   ═══════════════════════════════════════════════ *)

private
let default_fuel : nat = 100

(** Collect all [@@simp] lemmas from the environment and build state. *)
private
let mk_state (extras : list term) (use_global : bool) (fuel : nat) : Tac simp_state =
  let global_lems =
    if use_global then
      let ses = lookup_attr_ses (`simp) (cur_env ()) in
      filter_map parse_simp_sigelt ses
    else []
  in
  let extra_lems = filter_map parse_simp_term extras in
  let all_lems = global_lems @ extra_lems in
  let (idx, unidx) = build_simp_index all_lems in
  {
    index     = idx;
    unindexed = unidx;
    extras    = [];
    changed   = alloc false;
    fuel      = fuel;
    dbg       = debugging ();
  }

(* ═══════════════════════════════════════════════
   User-facing API
   ═══════════════════════════════════════════════ *)

(** Rewrite the goal using all in-scope [@@simp] lemmas.
    Applies rewrites bottom-up, repeating until fixed-point. *)
[@@plugin]
let simp_tac () : Tac unit =
  let st = mk_state [] true default_fuel in
  simp_loop st st.fuel

(** Rewrite using [@@simp] lemmas plus the given extra lemma terms. *)
[@@plugin]
let simp_with (extras : list term) : Tac unit =
  let st = mk_state extras true default_fuel in
  simp_loop st st.fuel

(** Rewrite using ONLY the given lemma terms. No [@@simp] discovery. *)
[@@plugin]
let simp_only (lems : list term) : Tac unit =
  let st = mk_state lems false default_fuel in
  simp_loop st st.fuel
