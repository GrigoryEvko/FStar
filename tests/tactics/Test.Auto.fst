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
module Test.Auto

open FStar.Tactics.V2
open FStar.Tactics.V2.Logic
open FStar.Tactics.Auto

(* ═══════════════════════════════════════════════
   Test: trivial goals
   ═══════════════════════════════════════════════ *)

let test_true : squash True =
  assert True by auto_tac ()

let test_refl (a : int) : Lemma (a == a) =
  assert (a == a) by auto_tac ()

(* ═══════════════════════════════════════════════
   Test: assumption from context
   ═══════════════════════════════════════════════ *)

let test_assumption (p : Type0) (h : squash p) : Lemma p =
  assert p by auto_tac ()

(* ═══════════════════════════════════════════════
   Test: conjunction splitting
   ═══════════════════════════════════════════════ *)

let test_and_trivial : squash (True /\ True) =
  assert (True /\ True) by auto_tac ()

let test_and_from_ctx (p q : Type0) (hp : squash p) (hq : squash q) : Lemma (p /\ q) =
  assert (p /\ q) by auto_tac ()

(* ═══════════════════════════════════════════════
   Test: implication introduction
   ═══════════════════════════════════════════════ *)

let test_implies_trivial : squash (True ==> True) =
  assert (True ==> True) by auto_tac ()

let test_implies_id (p : Type0) : Lemma (p ==> p) =
  assert (p ==> p) by auto_tac ()

(* ═══════════════════════════════════════════════
   Test: universal introduction
   ═══════════════════════════════════════════════ *)

let test_forall_trivial : squash (forall (x : int). True) =
  assert (forall (x : int). True) by auto_tac ()

(* ═══════════════════════════════════════════════
   Test: disjunction
   ═══════════════════════════════════════════════ *)

let test_or_left (p : Type0) (hp : squash p) : Lemma (p \/ False) =
  assert (p \/ False) by auto_tac ()

let test_or_right (p : Type0) (hp : squash p) : Lemma (False \/ p) =
  assert (False \/ p) by auto_tac ()

(* ═══════════════════════════════════════════════
   Test: nested propositions
   ═══════════════════════════════════════════════ *)

let test_nested_and (p q : Type0) (hp : squash p) (hq : squash q) : Lemma ((p /\ q) /\ True) =
  assert ((p /\ q) /\ True) by auto_tac ()

let test_nested_impl (p q : Type0) : Lemma (p ==> q ==> p) =
  assert (p ==> q ==> p) by auto_tac ()

(* ═══════════════════════════════════════════════
   Test: hint-based backward chaining
   ═══════════════════════════════════════════════ *)

assume val p : Type0
assume val q : Type0
assume val r : Type0

[@@auto]
assume val p_imp_q : squash p -> Lemma q

[@@auto]
assume val q_imp_r : squash q -> Lemma r

let test_chain (hp : squash p) : Lemma r =
  assert r by auto_tac ()

(* ═══════════════════════════════════════════════
   Test: auto_with extra hints
   ═══════════════════════════════════════════════ *)

assume val s : Type0
assume val r_imp_s : squash r -> Lemma s

let test_auto_with (hp : squash p) : Lemma s =
  assert s by auto_with [(`r_imp_s)]

(* ═══════════════════════════════════════════════
   Test: deep nesting
   ═══════════════════════════════════════════════ *)

let test_deep_nesting (p q : Type0) (hp : squash p) (hq : squash q)
  : Lemma ((p /\ q) /\ (q /\ p)) =
  assert ((p /\ q) /\ (q /\ p)) by auto_tac ()

let test_forall_and_implies (p : int -> Type0) (h : squash (forall x. p x))
  : Lemma (forall y. p y) =
  assert (forall y. p y) by auto_tac ()
