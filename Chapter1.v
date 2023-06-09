(*** * Chapter 1 **)

Require Export Coq.Init.Notations.
From Coq Require Export Ltac.

(** ** Reserved notations *)

Reserved Notation "A → B" (at level 99, B at level 200, right associativity).
Reserved Notation "x ,, y" (at level 60, right associativity).
Reserved Notation "X ⨿ Y" (at level 50, left associativity).
Reserved Notation "A × B" (at level 75, right associativity).
Reserved Notation "g ∘ f" (at level 40, left associativity).
Reserved Notation "p @ q" (at level 60, right associativity).
Reserved Notation "! p" (at level 50, left associativity).
Reserved Notation "p #" (at level 60).
Reserved Notation "f ~ g" (at level 70, no associativity).
Reserved Notation "X ≃ Y" (at level 80, no associativity).

(** ** Basic types *)

(** *** Universe *)

Notation UU := Type.

(** *** Dependent product *)

Notation "'∏'  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.

Notation "A -> B" := (∏ (_ : A), B): type_scope.

Notation "A → B" := (∏ (_ : A), B): type_scope.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).

Definition idfun (A: UU): A → A := λ x: A, x.

Definition swap {A B C: UU} (f: A → B → C) : B → A → C := λ (b: B) (a: A), f a b.

(** *** Empty type *) 

Inductive empty : UU := .

Notation "∅" := empty: type_scope.

(** *** The one-element type *)

Inductive unit: UU :=
  tt: unit.

(** *** Dependendent sum *)

Inductive total2 {A: UU} (B: A → UU) : UU := 
  tpair (a: A) (b: B a): total2 B.

Arguments total2_rect {_ _} _ _.

Notation "'∑'  x .. y , P" := (total2 (λ x, .. (total2 (λ y, P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.

Notation "x ,, y" := (tpair _ x y).

Definition pr1 {A: UU} {B: A → UU} 
  : (∑ a, B a) → A := total2_rect (λ _, A) (λ a b, a).

Definition pr2 {A: UU} {B: A → UU}
  : ∏ (p: total2 B), B (pr1 p) := total2_rect (λ a, B (pr1 a)) (λ a b, b).

Definition choiceaxiom {A B: UU} {R: A → B → UU} (g: ∏ x: A, ∑ y: B, R x y)
  : ∑ f: A → B, ∏ a: A, R a (f a)
  := tpair (λ f: A → B, ∏ a: A, R a (f a)) (λ a: A, pr1 (g a)) (λ a: A, pr2 (g a)).  

(** *** Coproduct *)

Inductive coprod (A B: UU): UU :=
  | inl : A → coprod A B
  | inr : B → coprod A B.

Arguments inl {_ _} _.
Arguments inr {_ _} _.

Notation "A ⨿  B" := (coprod A B).

(** *** Natural number type *)

Inductive nat : UU :=
  | O : nat
  | S : nat -> nat.

Notation "0" := (O).

Definition add (m n: nat): nat.
Proof.
  induction m.
  - exact n.
  - exact (S IHm).
Defined.

Declare Scope nat_scope.
Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.

Notation "x + y" := (add x y) : nat_scope.

(** *** Identity type *)

(** Unbased path type *)

Inductive paths {A: UU} (a: A): A → UU :=
  idpath: paths a a.
  
Notation "a = b" := (paths a b): type_scope.

Lemma paths_rect_gen {A: UU} (C: ∏ a b: A, a = b → UU) (c: ∏ a: A, C a a (idpath a))
  : ∏ (x y: A) (p: x = y), C x y p.
Proof.
  intro.
  exact (paths_rect A x (C x) (c x)).
Defined.

Lemma paths_rect_gen_simpl: ∏ {A : UU} (P : ∏ x y : A, x = y → UU) (refl: ∏ (x: A), P x x (idpath x)),
  ∏ (x: A), paths_rect_gen P refl x x (idpath x) = refl x.
Proof. 
  intros.
  apply idpath.
Defined.

Declare Scope paths_scope.
Delimit Scope paths_scope with paths.
Bind Scope paths_scope with paths.

(** Based path type *)

Inductive paths' {A: UU}: A → A → UU :=
  idpath' (a: A): paths' a a.

Lemma paths'_rect_based {A: UU} (a: A) (C: ∏ y: A, paths' a y → UU) (c: C a (idpath' a))
  : ∏ (y: A) (p: paths' a y), C y p.
Proof.
  intros.
  revert a y p C c.
  refine (paths'_rect _ _ _).
  intros.
  exact c.
Defined.

(* A variant using the induction tactic *)

Lemma paths'_rect_based' {A: UU} (a: A) (C: ∏ y: A, paths' a y → UU) (c: C a (idpath' a))
  : ∏ (y: A) (p: paths' a y), C y p.
Proof.
  intros.
  induction p.
  exact c.
Defined.

Goal @paths'_rect_based = @paths'_rect_based'.
Proof. apply idpath. Defined.

(** ** Derived types *)

(** *** Product *)

Definition prod (A B: UU): UU :=  ∑ (_: A),  B.

Notation "A × B" := (prod A B).

Definition prod_pr1 {A B: UU}: A × B → A := pr1.

Definition prod_pr2 {A B: UU}: A × B → B := pr2.

Definition prod_uniq {A B: UU} (x: A × B): (pr1 x ,, pr2 x) = x.
Proof.
  induction x.
  apply idpath.
Defined.

(** *** Boolean type *)

Definition bool := unit ⨿ unit.

Definition false: bool := inl tt.
Definition true: bool := inr tt.

(** ** Exercises *)

(** *** Execercise 1.1 *)

Definition funcomp {A B C: UU} (g: B → C) (f: A → B): A → C := λ x: A, g (f x).

Notation "g ∘ f" := (funcomp g f).

Theorem funcomp_assoc {A B C D: UU} (h: C → D) (g: B → C) (f: A → B) 
  : h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof.
  apply idpath.
Defined.

(** *** Exercise 1.3  *)

Theorem prod_myrect {A B: UU} (P : A × B → UU) (g: ∏ (a : A) (b : B), P (a ,, b))
   : ∏ t: A × B, P t.
Proof.
  intro t.
  pose (tpair := prod_uniq t).
  induction tpair.
  apply g.
Defined.

Definition total2_uniq {A: UU} {B: A → UU} (x: ∑ a: A, B a): (pr1 x ,, pr2 x) = x.
Proof.
  induction x.
  apply idpath.
Defined.

Definition total2_myrect {A: UU} {B: A → UU}
   (P : total2 B → UU) (g: ∏ (a : A) (b : B a), P (a,, b))
   : ∏ t : ∑ y, B y, P t.
Proof.
  intro t.
  pose (tpair := total2_uniq t).
  induction tpair.
  apply g.
Defined.
