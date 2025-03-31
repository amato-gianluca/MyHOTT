(*** * Chapter 1 **)

Require Export Init.

(** ** Section 1.3: Universes and families *)

Notation UU := Type.

(** ** Section 1.4: Dependent function types *)

Notation "∏ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.

Notation "A -> B" := (∏ (_ : A), B)
  (at level 99, B at level 200, right associativity) : type_scope.

Notation "A → B" := (A -> B)
  (at level 99, B at level 200, right associativity) : type_scope.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).

Definition idfun (A: UU): A → A := λ x: A, x.

Definition swap {A B C: UU} (g: A → B → C): B → A → C := λ (b: B) (a: A), g a b.

(** ** Section 1.5: Product types
We only introduce the unit type, since the product type is a special case of
the dependent pair type.
*)

Inductive unit: UU :=
  tt: unit.

(** ** Section 1.6: Dependent pair types *)

(* In UniMath this is a record type in order to use primitive projection and
force definitional eta-expansion. *)
Inductive total2 {A: UU} (B: A → UU): UU :=
  tpair (a: A) (b: B a): total2 B.

Arguments total2_rect {_ _} _ _.
Arguments tpair {_ _} _ _.

Notation "∑ x .. y , P" := (total2 (λ x, .. (total2 (λ y, P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.

Notation "A × B" := (∑ (_: A), B)
  (at level 75, right associativity) : type_scope.

Notation "x ,, y" := (tpair x y)
  (at level 60, right associativity).

Definition pr1 {A: UU} {B: A → UU}
  : (∑ a, B a) → A := total2_rect (λ _, A) (λ a b, a).

Definition pr2 {A: UU} {B: A → UU}
  : ∏ (p: total2 B), B (pr1 p) := total2_rect (λ a, B (pr1 a)) (λ a b, b).

(** The constructive choice axiom *)

Definition ac {A B: UU} {R: A → B → UU} (g: ∏ x: A, ∑ y: B, R x y)
  : ∑ f: A → B, ∏ x: A, R x (f x)
  := tpair (λ x: A, pr1 (g x)) (λ x: A, pr2 (g x)).

(** ** Section 1.7: Coproduct types *)

Inductive coprod (A B: UU): UU :=
  | ii1 : A → coprod A B
  | ii2 : B → coprod A B.

Arguments coprod_rect {_ _} _ _ _ _.
Arguments ii1 {_ _} _.
Arguments ii2 {_ _} _.

Notation "A ⨿ B" := (coprod A B)
  (at level 50, left associativity): type_scope.

Inductive empty : UU := .

(** ** Section 1.8: The type of booleans *)

Inductive bool: UU :=
  | false: bool
  | true: bool.

(** ** Section 1.9: The natural numbers *)

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
  - exact (idfun nat).
  - exact (λ x, S (add_m1 x)).
Defined.

Notation "x + y" := (add x y) (at level 50, left associativity) : nat_scope.

(**
Version of double using the induction principle instead of the
induction tactic.
*)

Definition double'(n: nat): nat
  := nat_rect (λ _, nat) 0 (λ n1 double'_n1, S (S double'_n1)) n.

(** Version of add inducting on the type nat instead of nat → nat. *)
Definition add' (m n: nat): nat.
Proof.
  induction m as [|_ add_m1_n].
  - exact n.
  - exact (S add_m1_n).
Defined.

(** ** Section 1.11: Propositions as types *)

Definition neg (A: UU) := A → empty : UU.

Notation "¬ A" := (neg A) (at level 35, right associativity) : type_scope.
Notation "¬¬ A" := (¬ (¬ A)) (at level 35, right associativity) : type_scope.

(** Some logic proofs *)

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

(** ** Section 1.12: Identity types *)

(** *** The based path type *)

Inductive paths {A: UU} (a: A): A → UU :=
  refl: paths a a.

Notation "a = b" := (paths a b) (at level 70, no associativity) : type_scope.

Notation "a != b" := (¬ (a = b)) (at level 70) : type_scope.

(**
Proof that the based path space is propositionally equal to the self loop.
*)

Lemma paths_based_space (A: UU) (x y: A) (p: x = y)
  : @paths (∑ (y : A), x = y) (y,, p) (x,, refl _).
Proof.
  induction p.
  apply refl.
Defined.

(** Proof that based path types can prove the free path induction principle. *)

Lemma paths_rect_free {A: UU} (C: ∏ x y: A, x = y → UU)
  (c: ∏ x: A, C x x (refl _))
  : ∏ (x y: A) (p: x = y), C x y p.
Proof.
  intro.
  exact (paths_rect A x (C x) (c x)).
Defined.

Lemma paths_rect_free_simpl {A : UU} (C : ∏ x y : A, x = y → UU)
  (c: ∏ x: A, C x x (refl x)) (x: A)
  : paths_rect_free C c x x (refl x) = c x.
Proof.
  apply refl.
Defined.

(** *** The free path type *)

Inductive paths_free {A: UU}: A → A → UU :=
  refl' (a: A): paths_free a a.

(**
Proof that the free path space is propositionally equal to the self loop.
*)

Lemma paths_free_space (A: UU) (x y: A) (p: paths_free x y)
  : @paths_free (∑ (x y : A), paths_free x y) (x,, y,, p) (x,, x,, refl' x).
Proof.
  pose (P := λ (x y: A) (p: paths_free x  y),
    @paths_free (∑ (x y : A), paths_free x y) (x,, y,, p) (x,, x,, refl' x)).
  apply (paths_free_rect A P).
  intros.
  apply refl'.
Defined.

(** Proof that free path types can prove the based path induction principle. *)

Lemma paths_free_rect_based {A: UU} (x: A) (C: ∏ y: A, paths_free x  y → UU)
  (c: C x (refl' x))
  : ∏ (y: A) (p: paths_free x y), C y p.
Proof.
  intros.
  revert C c.
  pose (P := λ (x y: A) (p: paths_free x y),
    ∏ (C: ∏ (y0: A), paths_free x y0 → UU), C x (refl' x) → C y p).
  apply (paths_free_rect A P).
  unfold P.
  intros.
  assumption.
Defined.

(** Proof that free path types can prove the based path induction principle.

Shorter version using the refine tactic. *)

Lemma paths_free_rect_based' {A: UU} (x: A) (C: ∏ y: A, paths_free x y → UU)
  (c: C x (refl' x))
  : ∏ (y: A) (p: paths_free x y), C y p.
Proof.
  intros.
  revert x y p C c.
  refine (paths_free_rect _ _ _).
  intros.
  assumption.
Defined.

Lemma paths_free_rect_based_simpl {A: UU} (x: A)
  (C: ∏ y: A, paths_free x y → UU) (c: C x (refl' x))
  : paths_free_rect_based x C c x (refl' x) = c.
Proof.
  apply refl.
Defined.

(** ** Uniqueness proofs
These are propositional uniqueness results which are provable by the induction
principle, but do not hold definitionally.
*)

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

Theorem uniq_sum {A:UU} {B: A → UU} (x: total2 B): (pr1 x ,, pr2 x) = x.
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

(** ** Exercises *)

(** *** Exercise 1.1 *)

Definition funcomp {A B C: UU} (g: B → C) (f: A → B): A → C := λ x: A, g (f x).

Notation "g ∘ f" := (funcomp g f) (at level 40, left associativity)
  : function_scope.

Theorem funcomp_assoc {A B C D: UU} (h: C → D) (g: B → C) (f: A → B)
  : h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof.
  apply refl.
Defined.

(** *** Exercise 1.2 *)

Local Definition prod_myrec {A B C: UU} (g: A → B → C)
  : A × B → C := λ x, g (pr1 x) (pr2 x).

Local Theorem prod_myrec_comp {A B C: UU} (g: A → B → C) (a: A) (b: B)
  : prod_myrec g (a ,, b) = g a b.
Proof.
  apply refl.
Defined.

Local Definition sum_myrec {A: UU} {B: A → UU} {C: UU}
  (g: ∏ (a: A) (b: B a), C)
  : (∑ (a: A), B a) → C := λ x, g (pr1 x) (pr2 x).

Local Theorem sum_myrec_comp {A: UU} {B: A → UU} {C: UU}
  (g: ∏ (a: A) (b: B a), C) (a: A) (b: B a)
  : sum_myrec g (a ,, b) = g a b.
Proof.
  apply refl.
Defined.

(** *** Exercise 1.3 *)

Local Definition prod_myrect {A B: UU} (P: A × B → UU)
  (g: ∏ (a: A) (b: B), P (a ,, b))
  : ∏ t: A × B, P t.
Proof.
  intro t.
  pose (tpair := uniq_sum t).
  induction tpair.
  apply g.
Defined.

Local Theorem prod_myrect_comp {A B: UU} (P: A × B → UU)
  (g: ∏ (a: A) (b: B), P (a ,, b)) (a: A) (b: B)
  : prod_myrect P g (a,, b) = g a b.
Proof.
  apply refl.
Defined.

Local Definition sum_myrect {A: UU} {B: A → UU} (P : total2 B → UU)
  (g: ∏ (a : A) (b : B a), P (a,, b))
  : ∏ t : ∑ y, B y, P t.
Proof.
  intro t.
  pose (tpair := uniq_sum t).
  induction tpair.
  apply g.
Defined.

Local Definition sum_myrect_comp {A: UU} {B: A → UU} (P : total2 B → UU)
  (g: ∏ (a : A) (b : B a), P (a,, b)) (a: A) (b: B a)
  : sum_myrect P g (a,, b) = g a b.
Proof.
  apply refl.
Defined.

(** *** Exercise 1.4 *)

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
What we need is the lemma nat_myrecaux_compsucc' later, but I cannot find
a way to solve this is a simple way without resorting to stuff in Chapter 2.
*)

Local Theorem nat_myrecaux_compsucc' {C: UU} (c0: C) (cs: nat → C → C) (n: nat)
  : nat_myrecaux c0 cs (S n) = S n,, cs n (pr2 (nat_myrecaux c0 cs n)).
Abort.

(** *** Exercise 1.5
Alternative definition of coproducts using bool.
*)

Local Definition coprod' (A B: UU) := ∑ (x: bool), (bool_rect (λ _, UU) A B x).

Local Definition inl' {A B: UU} (a: A): coprod' A B := false ,, a.

Local Definition inr' {A B: UU} (b: B): coprod' A B := true ,,  b.

Local Definition coprod'_rect (A B : UU) (P : coprod' A B → UU):
  (∏ a : A, P (inl' a)) → (∏ b : B, P (inr' b)) → ∏ c : coprod' A B, P c.
Proof.
  intros H1 H2 x.
  induction x as [tag v].
  induction tag.
  cbn in v.
  - exact (H1 v).
  - exact (H2 v).
Defined.

(** *** Exercise 1.6
Alternative definition of products using bool. Unfortunately, the induction
priciple requires function extensionality, hence it is delayed until Chapter 2.
*)

Local Definition prod' (A B: UU) := ∏ (x: bool), (bool_rect (λ _, UU) A B x).

Local Definition pair' {A B: UU} (a: A) (b: B): prod' A B
  := bool_rect (bool_rect (λ _, UU) A B) a b.

Local Definition pr1' {A B: UU} (p: prod' A B): A := p false.

Local Definition pr2' {A B: UU} (p: prod' A B): B := p true.

Local Definition prod'_rect (A B : UU) (P : prod' A B → UU):
  (∏ (a: A) (b: B), P (pair' a b)) → ∏ p : prod' A B, P p.
Proof.
  intros H p.
Abort.

(** *** Exercise 1.7
The requires concept introduced later, so it is delayed until Chapter 3.
*)

(** *** Exercise 1.8
This requires operating with identities, so it is delayed until Chapter 2.
*)

(** *** Exercise 1.9
This requires operating with identities, so it is delayed until Chapter 2.
*)

(** *** Exercise 1.10 *)

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

(** *** Exercise 1.11 *)

Local Theorem triple_neg (A: UU): ¬ (¬ (¬ A)) → ¬ A.
Proof.
  intros TN a.
  pose (DN := λ na: ¬ A, na a).
  exact (TN DN).
Defined.

(** *** Exercise 1.12 *)

Local Theorem taut1 (A B: UU): A → (B → A).
Proof.
  exact (λ a b, a).
Defined.

Local Theorem taut2 (A: UU): A → (¬ (¬ A)).
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

(** *** Exercise 1.13 *)

Local Theorem constructive_em (P: UU): ¬ (¬(P ⨿ ¬P)).
Proof.
  intro negem.
  pose (negp := λ p: P, negem (ii1 p)).
  exact (negem (ii2 negp)).
Defined.

(** *** Exercise 1.15 *)

Local Theorem iid {A: UU} {x y: A} (p: x = y) (C: A → UU): C x → C y.
Proof.
  induction p.
  apply idfun.
Defined.

(** *** Exercise 1.16
This requires operating with identities, so it is delayed until Chapter 2.
*)
