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
module Test.Simp

open FStar.Tactics.V2
open FStar.Tactics.Simp

(* ═══════════════════════════════════════════════
   Basic unconditional rewrite lemmas
   ═══════════════════════════════════════════════ *)

[@@simp]
let add_zero_r (x : int) : Lemma (x + 0 == x) = ()

[@@simp]
let add_zero_l (x : int) : Lemma (0 + x == x) = ()

[@@simp]
let mul_one_r (x : int) : Lemma (op_Multiply x 1 == x) = ()

[@@simp]
let mul_one_l (x : int) : Lemma (op_Multiply 1 x == x) = ()

[@@simp]
let mul_zero_r (x : int) : Lemma (op_Multiply x 0 == 0) = ()

[@@simp]
let mul_zero_l (x : int) : Lemma (op_Multiply 0 x == 0) = ()

(* ═══════════════════════════════════════════════
   Test: basic simp_tac usage
   ═══════════════════════════════════════════════ *)

let test_add_zero (a : int) : Lemma (a + 0 == a) =
  assert (a + 0 == a) by simp_tac ()

let test_mul_one (a : int) : Lemma (op_Multiply a 1 == a) =
  assert (op_Multiply a 1 == a) by simp_tac ()

let test_mul_zero (a : int) : Lemma (op_Multiply a 0 == 0) =
  assert (op_Multiply a 0 == 0) by simp_tac ()

let test_add_zero_left (a : int) : Lemma (0 + a == a) =
  assert (0 + a == a) by simp_tac ()

(* ═══════════════════════════════════════════════
   Test: nested rewrites (fixed-point iteration)
   ═══════════════════════════════════════════════ *)

let test_nested (a : int) : Lemma (op_Multiply (a + 0) 1 == a) =
  assert (op_Multiply (a + 0) 1 == a) by simp_tac ()

let test_deeply_nested (a : int) : Lemma (op_Multiply (op_Multiply a 1 + 0) 1 == a) =
  assert (op_Multiply (op_Multiply a 1 + 0) 1 == a) by simp_tac ()

(* ═══════════════════════════════════════════════
   Test: multiple occurrences in one goal
   ═══════════════════════════════════════════════ *)

let test_multi_occur (a b : int) : Lemma ((a + 0) + (b + 0) == a + b) =
  assert ((a + 0) + (b + 0) == a + b) by simp_tac ()

(* ═══════════════════════════════════════════════
   Test: simp_only with explicit lemmas
   ═══════════════════════════════════════════════ *)

let my_lemma (x : int) : Lemma (x + 0 == x) = ()

let test_simp_only (a : int) : Lemma (a + 0 == a) =
  assert (a + 0 == a) by simp_only [(`my_lemma)]

(* ═══════════════════════════════════════════════
   Test: simp_with (global + extras)
   ═══════════════════════════════════════════════ *)

let extra_lemma (x : int) : Lemma (x - 0 == x) = ()

let test_simp_with (a : int) : Lemma ((a + 0) - 0 == a) =
  assert ((a + 0) - 0 == a) by simp_with [(`extra_lemma)]

(* ═══════════════════════════════════════════════
   Test: boolean/propositional rewrites
   ═══════════════════════════════════════════════ *)

[@@simp]
let and_true_r (p : bool) : Lemma ((p && true) == p) = ()

[@@simp]
let and_false_r (p : bool) : Lemma ((p && false) == false) = ()

[@@simp]
let or_false_r (p : bool) : Lemma ((p || false) == p) = ()

[@@simp]
let or_true_r (p : bool) : Lemma ((p || true) == true) = ()

[@@simp]
let not_not (p : bool) : Lemma (not (not p) == p) = ()

let test_bool_simp (b : bool) : Lemma ((b && true) == b) =
  assert ((b && true) == b) by simp_tac ()

let test_bool_or (b : bool) : Lemma ((b || false) == b) =
  assert ((b || false) == b) by simp_tac ()

let test_not_not (b : bool) : Lemma (not (not b) == b) =
  assert (not (not b) == b) by simp_tac ()

(* ═══════════════════════════════════════════════
   Test: list rewrites
   ═══════════════════════════════════════════════ *)

open FStar.List.Tot.Base
open FStar.List.Tot.Properties

[@@simp]
let append_nil_r (#a : Type) (l : list a) : Lemma (l @ [] == l) =
  append_l_nil l

let test_list_append_nil (l : list int) : Lemma (l @ [] == l) =
  assert (l @ [] == l) by simp_tac ()

(* ═══════════════════════════════════════════════
   Test: user-defined function rewrites
   ═══════════════════════════════════════════════ *)

let double (x : int) : int = x + x
let quadruple (x : int) : int = double (double x)

[@@simp]
let double_zero (_:unit) : Lemma (double 0 == 0) = ()

let test_double_zero : squash (double 0 == 0) =
  assert (double 0 == 0) by simp_tac ()

(* ═══════════════════════════════════════════════
   Test: simp does not fail on already-simplified goals
   ═══════════════════════════════════════════════ *)

let test_noop (a b : int) : Lemma (a + b == a + b) =
  assert (a + b == a + b) by simp_tac ()
