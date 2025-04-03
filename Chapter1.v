(*** * Chapter 1. Type theory.  **)

Require Export Init.

(** ** Section 1.3: Universes and families. *)

(** *** Notation for the universe. *)

Notation UU := Type.

(** ** Section 1.4: Dependent function types. *)

(** *** Notations for (dependent) functions. *)

Notation "∏ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.

Notation "A -> B" := (∏ _ : A, B)
  (at level 99, B at level 200, right associativity) : type_scope.

Notation "A → B" := (A -> B)
  (at level 99, B at level 200, right associativity) : type_scope.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).

(** *** Identity function. *)

Definition fun_id (A: UU): A → A := λ x, x.

(** Makes [simpl], [cbn], etc. unfold [fun_id X x] but not [fun_id X]. *)

Arguments fun_id _ _ /.

(** *** Fibration over the base [A]. *)

Definition fib (A: UU): UU := ∏ x: A, UU.

(** *** Section of a fibration. *)

Definition sec {A: UU} (P: fib A): UU := ∏ x: A, P x.

(** *** Composition of a function and a section.
It also work for composition of two functions. *)

Definition fun_comp {A B: UU} {P: ∏ x: B, UU} (g: ∏ x: B, P x) (f: A → B)
  : ∏ x: A, P (f x) := λ x: A, g (f x).

Arguments fun_comp _ _ _/.

Notation "g ∘ f" := (fun_comp g f) (at level 40, left associativity)
  : function_scope.

(** *** The swap function. *)
Definition swap {A B C: UU} (g: A → B → C): B → A → C := λ b a, g a b.

(** ** Section 1.5: Product types.
We only introduce the unit type, since the product type is a special case of
the dependent pair type. *)

Inductive unit: UU :=
  tt: unit.

(** ** Section 1.6: Dependent pair types. *)

(** *** Dependent pair.

In UniMath this is a record type in order to use primitive projection and
force definitional eta-expansion. Moreover, projections in records seems to
be beta-reduced whenever possible.

The name [fib_total] is used because this is the total space of a fibration. *)

Inductive fib_total {A: UU} (B: fib A): UU :=
  tpair (a: A) (b: B a): fib_total B.

Arguments fib_total_rect {_ _}.

Arguments tpair {_ _}.

(** *** Notations for dependent pair. *)

Notation "∑ x .. y , P" := (fib_total (λ x, .. (fib_total (λ y, P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.

Notation "A × B" := (∑ (_: A), B)
  (at level 75, right associativity) : type_scope.

Notation "x ,, y" := (tpair x y)
  (at level 60, right associativity).

(** *** Projections for dependent pair. *)

Definition pr1 {A: UU} {B: fib A}
  : (∑ a, B a) → A := fib_total_rect (λ _, A) (λ a b, a).

Definition pr2 {A: UU} {B: A → UU}
  : ∏ (p: fib_total B), B (pr1 p) := fib_total_rect (λ a, B (pr1 a)) (λ a b, b).

(** *** The constructive choice axiom. *)

Definition ac {A B: UU} {R: A → B → UU} (g: ∏ x: A, ∑ y: B, R x y)
  : ∑ f: A → B, ∏ x: A, R x (f x)
  := tpair (λ x: A, pr1 (g x)) (λ x: A, pr2 (g x)).

(** ** Section 1.7: Coproduct types. *)

(** *** Binary coproduct. *)

Inductive coprod (A B: UU): UU :=
  | ii1 : A → coprod A B
  | ii2 : B → coprod A B.

Arguments coprod_rect {_ _} _ _ _ _.
Arguments ii1 {_ _} _.
Arguments ii2 {_ _} _.

Notation "A ⨿ B" := (coprod A B)
  (at level 50, left associativity): type_scope.

(** *** The empty type. *)

Inductive empty : UU := .

(** ** Section 1.8: The type of booleans. *)

Inductive bool: UU :=
  | false: bool
  | true: bool.

(** ** Section 1.9: The natural numbers. *)

Inductive nat : UU :=
  | O : nat
  | S : nat -> nat.

Open Scope nat_scope.

Notation "0" := O : nat_scope.
Notation "1" := (S 0) : nat_scope.
Notation "2" := (S 1) : nat_scope.
Notation "3" := (S 2) : nat_scope.

Definition double (n: nat): nat.
Proof.
  induction n as [|n1 double_n1].
  - exact 0.
  - exact (S (S double_n1)).
Defined.

Definition add (m: nat): nat → nat.
Proof.
  induction m as [|_ add_m1].
  - exact (fun_id nat).
  - exact (λ x, S (add_m1 x)).
Defined.

Notation "x + y" := (add x y) (at level 50, left associativity) : nat_scope.

(** Version of [double] using the induction principle instead of the
induction tactic. *)

Definition double'(n: nat): nat
  := nat_rect (λ _, nat) 0 (λ n1 double'_n1, S (S double'_n1)) n.

(** Version of add inducting on the type [nat] instead of [nat → nat]. *)

Definition add' (m n: nat): nat.
Proof.
  induction m as [|_ add_m1_n].
  - exact n.
  - exact (S add_m1_n).
Defined.

(** ** Section 1.11: Propositions as types. *)

(** *** Negation. *)

Definition neg (A: UU) := A → empty : UU.

Notation "¬ A" := (neg A) (at level 35, right associativity) : type_scope.

(** *** Some logic proofs. *)

Goal ∏ (A B: UU), (¬ A × ¬ B) → ¬ (A ⨿ B).
Proof.
  intros A B H x.
  induction x.
  - exact (pr1 H a).
  - exact (pr2 H b).
Qed.

Goal ∏ (A B: UU), ¬ (A ⨿ B) → (¬ A × ¬ B).
Proof.
  intros A B H.
  split.
  - intro a.
    exact (H (ii1 a)).
  - intro a.
    exact (H (ii2 a)).
Qed.

Goal ∏ (A: UU) (P Q: A → UU),
  (∏ (x: A), P x × Q x) → (∏ (x: A), P x) × (∏ (x: A), Q x).
Proof.
  intros A P Q H.
  apply tpair.
  - exact (λ x, pr1 (H x)).
  - exact (λ x, pr2 (H x)).
Qed.

(** ** Section 1.12: Identity types. *)

(** *** The based path type. *)

Inductive path {A: UU} (a: A): A → UU :=
  refl: path a a.

Notation "a = b" := (path a b) (at level 70, no associativity) : type_scope.

Notation "a != b" := (¬ (a = b)) (at level 70) : type_scope.

(** Proof that the based path space is propositionally equal to the self loop. *)

Lemma path_based_space (A: UU) (x y: A) (p: x = y)
  : @path (∑ (y : A), x = y) (y,, p) (x,, refl _).
Proof.
  induction p.
  apply refl.
Defined.

(** Proof that based path types can prove the free path induction principle. *)

Lemma path_rect_free {A: UU} (C: ∏ x y: A, x = y → UU)
  (c: ∏ x: A, C x x (refl _))
  : ∏ (x y: A) (p: x = y), C x y p.
Proof.
  intro.
  exact (path_rect A x (C x) (c x)).
Defined.

Lemma path_rect_free_simpl {A : UU} (C : ∏ x y : A, x = y → UU)
  (c: ∏ x: A, C x x (refl x)) (x: A)
  : path_rect_free C c x x (refl x) = c x.
Proof.
  apply refl.
Defined.

(** *** The free path type- *)

Inductive path_free {A: UU}: A → A → UU :=
  refl_free (a: A): path_free a a.

(** Proof that the free path space is propositionally equal to the self loop. *)

Lemma path_free_space (A: UU) (x y: A) (p: path_free x y)
  : @path_free (∑ (x y : A), path_free x y) (x,, y,, p) (x,, x,, refl_free x).
Proof.
  pose (P := λ (x y: A) (p: path_free x  y),
    @path_free (∑ (x y : A), path_free x y) (x,, y,, p) (x,, x,, refl_free x)).
  apply (path_free_rect A P).
  intros.
  apply refl_free.
Defined.

(** Proof that free path types can prove the based path induction principle. *)

Lemma path_free_rect_based {A: UU} (x: A) (C: ∏ y: A, path_free x y → UU)
  (c: C x (refl_free x))
  : ∏ (y: A) (p: path_free x y), C y p.
Proof.
  intros.
  revert C c.
  pose (P := λ (x y: A) (p: path_free x y),
    ∏ (C: ∏ (y0: A), path_free x y0 → UU), C x (refl_free x) → C y p).
  apply (path_free_rect A P).
  unfold P.
  intros.
  assumption.
Defined.

(** Shorter version of previous lemma using the refine tactic. *)

Lemma path_free_rect_based' {A: UU} (x: A) (C: ∏ y: A, path_free x y → UU)
  (c: C x (refl_free x))
  : ∏ (y: A) (p: path_free x y), C y p.
Proof.
  intros.
  revert x y p C c.
  refine (path_free_rect _ _ _).
  intros.
  assumption.
Defined.

Lemma path_free_rect_based_simpl {A: UU} (x: A)
  (C: ∏ y: A, path_free x y → UU) (c: C x (refl_free x))
  : path_free_rect_based x C c x (refl_free x) = c.
Proof.
  apply refl.
Defined.

(** ** Uniqueness proofs.
These are propositional uniqueness results which are provable by the induction
principle, but do not hold definitionally. *)

Theorem uniq_unit (x: unit): x = tt.
Proof.
  induction x.
  apply refl.
Defined.

Theorem uniq_prod {A B:UU} (x: A × B): (pr1 x ,, pr2 x) = x.
Proof.
  induction x.
  apply refl.
Defined.

Theorem uniq_sum {A:UU} {B: A → UU} (x: fib_total B): (pr1 x ,, pr2 x) = x.
Proof.
  induction x.
  apply refl.
Defined.

Theorem uniq_bool (x: bool): (x = false) ⨿ (x = true).
Proof.
  induction x.
  - apply ii1.
    apply refl.
  - apply ii2.
    apply refl.
Defined.

(** This is an alternative proof of propositional uniqueness which directly
uses the induction principle instead of the induction tactic. *)

Definition uniq_unit' (x: unit): x = tt.
Proof.
  apply (unit_rect (λ x, x = tt)).
  apply refl.
Defined.

(** ** Exercises. *)

(** *** Exercise 1.1. *)

Goal ∏ (A B C D: UU) (h: C → D) (g: B → C) (f: A → B),  h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof.
  intros.
  apply refl.
Defined.

Definition fun_comp_iter {A: UU} (f: A → A) (n: nat): A → A.
Proof.
  induction n.
  - exact (fun_id A).
  - exact (f ∘ IHn).
Defined.

(** *** Exercise 1.2. *)

Local Definition prod_myrec {A B C: UU} (g: A → B → C)
  : A × B → C := λ x, g (pr1 x) (pr2 x).

Local Theorem prod_myrec_comp {A B C: UU} (g: A → B → C) (a: A) (b: B)
  : prod_myrec g (a ,, b) = g a b.
Proof.
  apply refl.
Defined.

Local Definition sum_myrec {A: UU} {B: fib A} {C: UU}
  (g: ∏ (a: A) (b: B a), C)
  : (∑ (a: A), B a) → C := λ x, g (pr1 x) (pr2 x).

Local Theorem sum_myrec_comp {A: UU} {B: fib A} {C: UU}
  (g: ∏ (a: A) (b: B a), C) (a: A) (b: B a)
  : sum_myrec g (a ,, b) = g a b.
Proof.
  apply refl.
Defined.

(** *** Exercise 1.3. *)

Local Definition prod_myrect {A B: UU} (P: fib (A × B))
  (g: ∏ (a: A) (b: B), P (a ,, b))
  : sec P.
Proof.
  intro t.
  pose (tpair := uniq_sum t).
  induction tpair.
  apply g.
Defined.

Local Theorem prod_myrect_comp {A B: UU} (P: fib (A × B))
  (g: ∏ (a: A) (b: B), P (a ,, b)) (a: A) (b: B)
  : prod_myrect P g (a,, b) = g a b.
Proof.
  apply refl.
Defined.

Local Definition sum_myrect {A: UU} {B: fib A} (P : fib (fib_total B))
  (g: ∏ (a : A) (b : B a), P (a,, b))
  : sec P.
Proof.
  intro t.
  pose (tpair := uniq_sum t).
  induction tpair.
  apply g.
Defined.

Local Definition sum_myrect_comp {A: UU} {B: fib A} (P : fib (fib_total B))
  (g: ∏ (a : A) (b : B a), P (a,, b)) (a: A) (b: B a)
  : sum_myrect P g (a,, b) = g a b.
Proof.
  apply refl.
Defined.

(** *** Exercise 1.4. *)

Local Definition nat_myiter {C: UU} (c0: C) (cs: C → C): nat → C
  := nat_rect (λ _, C) c0 (λ _ prev, cs prev).

Local Theorem nat_myiter_compsucc {C: UU} (c0: C) (cs: C → C) (n: nat)
  : nat_myiter c0 cs (S n) = cs (nat_myiter c0 cs n).
Proof.
  apply refl.
Defined.

Local Definition nat_myrecaux {C: UU} (c0: C) (cs: nat → C → C): nat → (nat × C)
  := @nat_myiter (nat × C) (0,, c0) (λ p, S (pr1 p),, cs (pr1 p) (pr2 p)).

Local Theorem nat_myrecaux_comp0 {C: UU} (c0: C) (cs: nat → C → C)
  : nat_myrecaux c0 cs 0 = 0,, c0.
Proof.
  apply refl.
Defined.

Local Theorem nat_myrecaux_compsucc {C: UU} (c0: C) (cs: nat → C → C) (n: nat)
  : nat_myrecaux c0 cs (S n) = S (pr1 (nat_myrecaux c0 cs n)),,
      cs (pr1 (nat_myrecaux c0 cs n)) (pr2 (nat_myrecaux c0 cs n)).
Proof.
  apply refl.
Defined.

(**
What we need is the lemma [nat_myrecaux_compsucc'] later, but I cannot find
a way to solve this in a simple way without resorting to stuff in Chapter 2.
*)

Local Theorem nat_myrecaux_compsucc' {C: UU} (c0: C) (cs: nat → C → C) (n: nat)
  : nat_myrecaux c0 cs (S n) = S n,, cs n (pr2 (nat_myrecaux c0 cs n)).
Abort.

(** *** Exercise 1.5.
Alternative definition of coproducts using [bool]. *)

Local Definition coprod' (A B: UU) := ∑ (x: bool), (bool_rect (λ _, UU) A B x).

Local Definition inl' {A B: UU} (a: A): coprod' A B := false ,, a.

Local Definition inr' {A B: UU} (b: B): coprod' A B := true ,,  b.

Local Definition coprod'_rect {A B : UU} (P : fib (coprod' A B))
  (g1: ∏ a : A, P (inl' a)) (g2: ∏ b : B, P (inr' b))
  : sec P.
Proof.
  intro x.
  induction x as [tag v].
  induction tag.
  cbn in v.
  - exact (g1 v).
  - exact (g2 v).
Defined.

(** *** Exercise 1.6.
Alternative definition of products using [bool]. Unfortunately, the induction
priciple requires function extensionality, hence it is delayed until Chapter 2.
*)

Local Definition prod' (A B: UU) := ∏ (x: bool), (bool_rect (λ _, UU) A B x).

Local Definition pair' {A B: UU} (a: A) (b: B): prod' A B
  := bool_rect (bool_rect (λ _, UU) A B) a b.

Local Definition pr1' {A B: UU} (p: prod' A B): A := p false.

Local Definition pr2' {A B: UU} (p: prod' A B): B := p true.

Local Definition prod'_rect {A B : UU} (P : fib (prod' A B))
  (g: ∏ (a: A) (b: B), P (pair' a b))
  : sec P.
Proof.
  intros p.
Abort.

(** *** Exercise 1.7.
The requires concept introduced later, so it is delayed until Chapter 3.
*)

(** *** Exercise 1.8.
This requires operating with identities, so it is delayed until Chapter 2.
*)

(** *** Exercise 1.9.
This requires operating with identities, so it is delayed until Chapter 2.
*)

(** *** Exercise 1.10. *)

Definition ack (m n: nat): nat.
Proof.
  revert n.
  induction m as [|m ack_m].
  - exact (λ n, S n).
  - intro n.
    induction n as [|n ack_Sm_n].
    + exact (ack_m 1).
    + exact (ack_m ack_Sm_n).
Defined.

(** *** Exercise 1.11. *)

Local Theorem triple_neg (A: UU): ¬ ¬ ¬ A → ¬ A.
Proof.
  intros TN a.
  pose (DN := λ na: ¬ A, na a).
  exact (TN DN).
Defined.

(** *** Exercise 1.12. *)

Local Theorem taut1 (A B: UU): A → (B → A).
Proof.
  exact (λ a b, a).
Defined.

Local Theorem taut2 (A: UU): A → ¬ ¬ A.
Proof.
  exact (λ a na, na a).
Defined.

Local Theorem taut3 (A B: UU): (¬ A ⨿ ¬ B) → ¬ (A × B).
Proof.
  intros s p.
  induction s.
  - exact (a (pr1 p)).
  - exact (b (pr2 p)).
Defined.

(** *** Exercise 1.13. *)

Local Theorem constructive_em (P: UU): ¬  ¬ (P ⨿ ¬ P).
Proof.
  intro negem.
  pose (negp := λ p: P, negem (ii1 p)).
  exact (negem (ii2 negp)).
Defined.

(** *** Exercise 1.15.
Indiscernability of identicals. It will be called [transport] in
Chapter 2. *)

Local Theorem iid {A: UU} {x y: A} (p: x = y) (C: fib A): C x → C y.
Proof.
  induction p.
  apply fun_id.
Defined.

(** *** Exercise 1.16.
This requires operating with identities, so it is delayed until Chapter 2.
*)
