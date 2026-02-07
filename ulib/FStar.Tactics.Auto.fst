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

(** Depth-bounded backward proof search tactic for F*.

    Tag lemmas with [@@auto] for automatic discovery.
    Use [auto_tac()] in a [by (...)] block for automatic proof search.

    Strategy (at each depth level):
    1. [trivial]: solve True, reflexivity
    2. [assumption]: solve from context
    3. [split]: decompose conjunctions
    4. [l_intro]: introduce foralls and implications
    5. [left/right]: try disjunction branches
    6. [apply]: try [@@auto] lemmas + context hypotheses
*)
module FStar.Tactics.Auto

open FStar.Reflection.V2
open FStar.Reflection.V2.Formula
open FStar.Stubs.Reflection.V2.Data
open FStar.Stubs.Tactics.Common
open FStar.Tactics.Effect
open FStar.Stubs.Tactics.V2.Builtins
open FStar.Stubs.Tactics.Types
open FStar.Tactics.V2.SyntaxHelpers
open FStar.Tactics.V2.Derived
open FStar.Tactics.V2.SyntaxCoercions
open FStar.Tactics.V2.Logic
open FStar.Tactics.NamedView
open FStar.Tactics.Util

module L = FStar.List.Tot.Base
let (@) = L.op_At

(* ═══════════════════════════════════════════════
   Attribute
   ═══════════════════════════════════════════════ *)

(** Tag a lemma with [@@auto] for discovery by [auto_tac]. *)
irreducible let auto : unit = ()

(* ═══════════════════════════════════════════════
   Types
   ═══════════════════════════════════════════════ *)

noeq
type auto_hint = {
  ah_term : term;   (* The lemma/hypothesis term to apply *)
  ah_arity : nat;   (* Number of arguments (for apply depth) *)
}

(* ═══════════════════════════════════════════════
   Hint collection
   ═══════════════════════════════════════════════ *)

(** Extract the name of a sigelt. *)
private
let sigelt_name (se : sigelt) : Tac fv =
  match inspect_sigelt se with
  | Sg_Let {lbs} -> (
    match lbs with
    | [lb] -> lb.lb_fv
    | _ -> fail "auto: sigelt_name: multiple let bindings"
  )
  | Sg_Val {nm} -> pack_fv nm
  | _ -> fail "auto: sigelt_name: unsupported sigelt shape"

(** Count the number of arrow binders in a type. *)
private
let rec count_arrows (t : term) : Tac nat =
  match inspect t with
  | Tv_Arrow _ c -> (
    match inspect_comp c with
    | C_Total t' -> 1 + count_arrows t'
    | C_Lemma _ _ _ -> 0
    | _ -> 0
  )
  | _ -> 0

(** Parse a sigelt into an auto_hint. *)
private
let parse_auto_sigelt (se : sigelt) : Tac (option auto_hint) =
  try
    let fv = sigelt_name se in
    let tm = pack (Tv_FVar fv) in
    let typ = tc (cur_env ()) tm in
    let ar = count_arrows typ in
    Some { ah_term = tm; ah_arity = ar }
  with | _ -> None

(** Collect all [@@auto] hints from the environment. *)
private
let collect_hints () : Tac (list auto_hint) =
  let ses = lookup_attr_ses (`auto) (cur_env ()) in
  filter_map parse_auto_sigelt ses

(** Collect hypotheses from the local context as hints. *)
private
let context_hints () : Tac (list auto_hint) =
  let bs = cur_vars () in
  L.map (fun (b : binding) ->
    { ah_term = binding_to_term b; ah_arity = 0 }
  ) bs

(* ═══════════════════════════════════════════════
   Core search engine
   ═══════════════════════════════════════════════ *)

private
let default_depth : nat = 5

(** Try to solve by reflexivity / trivial. *)
private
let try_trivial () : Tac bool =
  match trytac trivial with
  | Some _ -> true
  | None ->
    match trytac (fun () -> norm [iota; zeta; primops; delta]; trivial ()) with
    | Some _ -> true
    | None -> false

(** Try to solve by finding a matching hypothesis in context. *)
private
let try_assumption () : Tac bool =
  match trytac assumption with
  | Some _ -> true
  | None -> false

(** Try applying a hint and recursively solving subgoals.
    Returns true on success, false on failure (with rollback). *)
private
let rec try_hint (depth : nat) (hints : list auto_hint) (h : auto_hint) : Tac bool =
  if depth = 0 then false
  else
    match trytac (fun () -> apply_lemma h.ah_term) with
    | None -> false
    | Some _ ->
      (* apply_lemma succeeded, now solve all generated subgoals *)
      solve_all (depth - 1) hints

(** Try each hint in order with backtracking. *)
and try_hints (depth : nat) (hints : list auto_hint) (hs : list auto_hint) : Tac bool =
  match hs with
  | [] -> false
  | h :: rest ->
    match trytac (fun () -> try_hint depth hints h) with
    | Some true -> true
    | _ -> try_hints depth hints rest

(** Main search: try all strategies at the current goal. *)
and auto_search (depth : nat) (hints : list auto_hint) : Tac unit =
  if depth = 0 then fail "auto: depth exhausted"
  else begin
    (* Strategy 1: trivial / reflexivity *)
    if try_trivial () then ()
    (* Strategy 2: exact hypothesis match *)
    else if try_assumption () then ()
    else begin
      let g = cur_goal () in
      match term_as_formula g with
      (* Strategy 3: conjunction — split and solve both sides *)
      | And _ _ ->
        split ();
        iterAll (fun () -> auto_search (depth - 1) hints)

      (* Strategy 4: implication — introduce and continue *)
      | Implies _ _ ->
        let _ = implies_intro () in
        auto_search (depth - 1) hints

      (* Strategy 5: universal — introduce and continue *)
      | Forall _ _ _ ->
        let _ = forall_intro () in
        auto_search (depth - 1) hints

      (* Strategy 6: disjunction — try left, then right *)
      | Or _ _ ->
        or_else
          (fun () -> left (); auto_search (depth - 1) hints)
          (fun () -> right (); auto_search (depth - 1) hints)

      (* Strategy 7: True *)
      | True_ -> trivial ()

      (* Strategy 8: try applying hints *)
      | _ ->
        let ctx = context_hints () in
        let all = ctx @ hints in
        if try_hints depth all all
        then ()
        else fail "auto: no applicable hint"
    end
  end

(** Solve all current goals via auto_search. *)
and solve_all (depth : nat) (hints : list auto_hint) : Tac bool =
  let n = ngoals () in
  if n = 0 then true
  else begin
    match trytac (fun () ->
      iterAll (fun () -> auto_search depth hints)
    ) with
    | Some _ -> true
    | None -> false
  end

(* ═══════════════════════════════════════════════
   User-facing API
   ═══════════════════════════════════════════════ *)

(** Automatic proof search using [@@auto] hints.
    Depth-bounded backward chaining with backtracking. *)
[@@plugin]
let auto_tac () : Tac unit =
  let hints = collect_hints () in
  auto_search default_depth hints

(** Automatic proof search with explicit depth limit. *)
[@@plugin]
let auto_with_depth (depth : nat) : Tac unit =
  let hints = collect_hints () in
  auto_search depth hints

(** Automatic proof search with extra hint terms. *)
[@@plugin]
let auto_with (extras : list term) : Tac unit =
  let hints = collect_hints () in
  let extra_hints = L.map (fun t -> { ah_term = t; ah_arity = 0 }) extras in
  auto_search default_depth (hints @ extra_hints)
