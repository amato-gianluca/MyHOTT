(** * Chapter 2. Homotopy type theory. *)

Require Export Chapter1.

(** ** Section 2.1: Types are higher groupoids. *)

(** *** Inverse of a path (Lemma 2.1.1 from the book). *)

Definition path_inv {A: UU} {x y: A} (p: x = y): y = x.
Proof.
  induction p.
  apply refl.
Defined.

Notation "! p" := (path_inv p) (at level 50, left associativity).

(** This is implemented using path induction instead of the induction tactic. *)

Local Definition path_inv' {A: UU} {x y: A} (p: x = y): (y = x).
Proof.
  pose (D := λ (x y: A) (p: x = y), y = x).
  pose (d := (λ x: A, refl _) : ∏ x: A, D x x (refl _) ).
  exact (path_rect_free D d x y p).
Defined.

(** *** Composition of paths (Lemma 2.1.2 from the book). *)

Definition path_comp {A: UU} {x y z: A} (p: x = y) (q: y = z): x = z.
Proof.
  induction p.
  induction q.
  apply refl.
Defined.

(** This is implemented using path induction instead of the induction tactic. *)

Local Definition path_comp' {A: UU} {x y z: A} (p: x = y) (q: y = z): x = z.
Proof.
  pose (D := λ (x y: A) (p: x = y), ∏ (z: A) (q: y = z), x = z).
  refine (path_rect_free D _  x y p z q).
  unfold D.
  pose (E := λ (x y : A) (p: x = y), x = y).
  pose (e := λ (x: A), refl x).
  exact (path_rect_free E e).
Defined.

Notation "p @ q" := (path_comp p q) (at level 60, right associativity).

(** A tacting for for simplifying proofs with path composition. *)

Ltac etrans := eapply path_comp.

(** *** [refl] is the left identity for path composition.
Since our definition of [path_comp] is symmetric, this only holds propositionally.
This is part of Lemma 2.1.4. *)

Lemma path_comp_lid {A: UU} {x y: A} (p: x = y): (refl _) @ p = p.
Proof.
  induction p.
  apply refl.
Defined.

(** *** [refl] is the right identity for path composition.
Since our definition of [path_comp] is symmetric, this only holds propositionally.
This is part of Lemma 2.1.4. *)

Lemma path_comp_rid{A: UU} {x y: A} (p: x = y): p @ (refl _) = p.
Proof.
  induction p.
  apply refl.
Defined.

(** *** [! p] is the right inverse of [p] w.r.t. path composition.
This is part of Lemma 2.1.4. *)

Lemma path_comp_rinv {A: UU} {x y: A} (p: x = y): p @ ! p = refl _.
Proof.
  induction p.
  apply refl.
Defined.

(** *** [! p] is left right inverse of [p] w.r.t. path composition.
This is part of Lemma 2.1.4. *)

Lemma path_comp_linv {A: UU} {x y: A} (p: x = y): !p @ p = refl _.
Proof.
  induction p.
  apply refl.
Defined.

(** *** Associativity of path composition.
This is part of Lemma 2.1.4. *)

Lemma path_comp_assoc {A: UU} {w x y z: A} (p: w = x) (q: x = y) (r: y = z)
  : p @ (q @ r) = (p @ q) @ r.
Proof.
  induction p.
  induction q.
  induction r.
  apply refl.
Defined.

(** A variant of the previous one, useful in the [apply] tactic. *)

Lemma path_comp_assoc' {A: UU} {w x y z: A} (p: w = x) (q: x = y) (r: y = z)
  : (p @ q) @ r = p @ (q @ r).
Proof.
  induction p.
  induction q.
  induction r.
  apply refl.
Defined.

(** *** Path inversion is involutive.
This is part of Lemma 2.1.4. *)

Lemma path_inv_inv {A: UU} {x y: A} (p: x = y): ! (! p) = p.
Proof.
  induction p.
  apply refl.
Defined.

(** *** Right whiskering of a path.
From [p = q] we get [p @ r = q @ r]. This corresponds to [pathcomp_cancel_right]
in UniMath, and may be used to cancel the [r] in an [apply] tactic. *)

Definition path_rwhiskering {A: UU} {x y z: A} {p q: x = y} (α: p = q) (r: y = z)
  : p @ r = q @ r.
Proof.
  induction r.
  exact (path_comp_rid _ @ α @ ! path_comp_rid _).
Defined.

Notation "α @> q" := (path_rwhiskering α q) (at level 40).

(** Version of [path_rwhiskering] using induction without resorting to previous
lemmas. There is often a choice between proving something by induction or
resorting to previous results. *)

Local Definition path_rwhiskering' {A: UU} {x y z: A}
  {p q: x = y} (α: p = q) (r: y = z)
  : p @ r = q @ r.
Proof.
  induction r, q, α.
  apply refl.
Defined.

(** *** Left whiskering of a path.
From [p = q] we get [l @ p = l @ q].  This corresponds to [pathcomp_cancel_left]
in UniMath, and may be used to cancel the [l] in an [apply] tactic. *)

Definition path_lwhiskering {A: UU} {x y z: A} {p q: x = y} (l: z = x) (α: p = q)
  : l @ p = l @ q.
Proof.
  induction l.
  exact (path_comp_lid _ @ α @ ! path_comp_lid _).
Defined.

Notation "p <@ α" := (path_lwhiskering p α) (at level 40).

(** *** Horizontal composition of paths.
From [p = q] and [r = s] we get [p @ r = q @ s]. *)

Definition path_horzcomp {A: UU} {x y z : A}
  {p q: x = y} {r s: y = z} (α: p = q) (β: r = s)
  : p @ r = q @ s := (α @> r) @ (q <@ β).

Notation "α ⋆ β" := (path_horzcomp α β) (at level 40, left associativity).

(** Alternative definition of horizontal composition. *)

Definition path_horzcomp' {A: UU} {x y z : A}
  {p q: x =y} {r s : y= z} (α: p = q) (β: r = s)
  : p @ r = q @s := (p <@ β) @ (α @> s).

Notation "α ⋆' β" := (path_horzcomp' α β)
  (at level 40, left associativity).

(** Equality of the two definitions of horizontal composition. *)

Lemma path_horzcomp_eq  {A: UU} {x y z : A}
  {p q: x = y} {r s: y= z} (α: p = q) (β: r = s)
  : α ⋆ β = α ⋆' β.
Proof.
  induction α.
  induction β.
  induction p.
  induction r.
  apply refl.
Defined.

(** *** Whiskering with path composition. *)

Lemma path_rwhiskering_comp {A: UU} {a b c d: A} {x y: a = b} (α: x = y)
  (p: b = c) (q: c = d)
  : α @> (p @ q) =  path_comp_assoc _ _ _ @ (α @> p @> q) @ path_comp_assoc' _ _ _.
Proof.
  induction q.
  induction p.
  induction α.
  induction x.
  apply refl.
Defined.

Lemma path_lwhiskering_comp {A: UU} {a b c d: A} {x y: c = d} (α: x = y)
  (p: a = b) (q: b = c)
  : (p @ q) <@ α  = path_comp_assoc' _ _ _ @ p <@ (q <@ α) @ path_comp_assoc _ _ _.
Proof.
  induction q.
  induction p.
  induction α.
  induction x.
  apply refl.
Defined.

(** *** Whiskering with path identity.
These equalities holds deifinitionally. *)

Goal ∏ {A: UU} {a b: A} {x y: a = b} (α: x = y),
  α @> refl _ = path_comp_rid _ @ α @ ! path_comp_rid _.
Proof.
  intros.
  apply refl.
Defined.

Goal ∏ {A: UU} {a b: A} {x y: a = b} (α: x = y),
  refl _ <@ α = path_comp_lid _ @ α @ ! path_comp_lid _.
Proof.
  intros.
  apply refl.
Defined.

(** *** Pointed type (Definition 2.1.7 from the book). *)

Definition ptype: UU := ∑ (A: UU), A.

Definition ptype_to_type: ptype → UU := pr1.

Coercion ptype_to_type: ptype >-> Sortclass.

(** *** Loop space of a pointed type (Definition 2.1.8 from the book). *)

Definition loop_space (X: ptype): ptype := ((pr2 X = pr2 X) ,, refl (pr2 X)).

(** We define Ω as a function over pointed types, as at the end of Section 2.1,
instead of using the ad-hoc definition in the middle of the same section. *)

Notation "'Ω' X" := (loop_space X) (at level 35, right associativity).

(** This in an example of application of the loop space. Note that, in order
for this to work, universe polymorphism of [ptype], [loop_space]
and fun_iter] is essential. *)

Goal Ω Ω (nat,, 0) =  (refl 0 = refl 0),, refl (refl 0).
Proof.
  apply refl.
Qed.

(** *** The Eckmann-Hilton theorem (Lemma 2.1.6 from the book). *)

Lemma path_horzcomp_trans1 {X: ptype} (α: Ω Ω X) (β: Ω Ω X)
  : α ⋆ β = α @ β.
Proof.
  unfold "⋆".
  induction X as [A a].
  simpl (pr2 (Ω (A,, a))) .
  change (α @> refl a) with (path_comp_rid (refl a) @ α @ ! (path_comp_rid (refl a))).
  change (refl a <@ β) with (path_comp_lid (refl a) @ β @ ! (path_comp_lid (refl a))).
  change (! path_comp_lid (refl a)) with  (path_comp_lid (refl a)).
  change (! path_comp_rid (refl a)) with  (path_comp_rid (refl a)).
  change (path_comp_rid (refl a)) with (refl (refl a)).
  change (path_comp_lid (refl a)) with (refl (refl a)).
  pose (res :=
    path_comp_assoc (refl (refl a) @ α @ refl (refl a)) (refl (refl a)) (β @ refl (refl a))
    @ path_comp_assoc _ _ _
    @ path_comp_rid _
    @ (! path_comp_assoc _ _ _ @> β)
    @ (path_comp_lid _ @> β)
    @ (! path_comp_assoc _ _ _ @> β)
    @ (α <@ (path_comp_rinv _) @> β)
    @ ((path_comp_rid _) @> β)
  ).
  exact res.
Defined.

(** Same lemma as before, but with a backward style proof. Moreover, we
collapse all [change] tactic in a single one. *)

Local Lemma path_horzcomp_trans1' {X: ptype} (α: Ω Ω X) (β: Ω Ω X)
  : α ⋆ β = α @ β.
Proof.
  induction X as [A a].
  change ((refl (refl a) @ α @ refl (refl a)) @ refl (refl a) @ β @ refl (refl a) = α @ β).
  etrans.
  apply path_comp_assoc.
  etrans.
  apply path_comp_assoc.
  etrans.
  apply path_comp_rid.
  apply path_rwhiskering.
  etrans.
  apply path_comp_assoc'.
  etrans.
  apply path_comp_lid.
  etrans.
  apply path_comp_assoc'.
  apply path_comp_rid.
Defined.

(**
Due to the use of symmetric [path_comp], the previous proofs are quite convoluted.
As an example, this would be the same proof using an asymmetric definition  of
[path_comp], where many equalities hold definitionally.

[[
Proof.
  unfold "⋆".
  cbn.
  eapply path_comp.
  - apply (! path_comp_assoc _ _ _).
  - apply refl.
Defined
]]
*)

Lemma path_horzcomp_trans2 {X: ptype} (α: Ω Ω X) (β: Ω Ω X)
  : α ⋆' β = β @ α.
Proof.
  induction X as [A a].
  change ((refl (refl a) @ β @ refl (refl a)) @ refl (refl a) @ α @ refl (refl a) = β @ α).
  pose (res :=
    path_comp_assoc (refl (refl a) @ β @ refl (refl a)) (refl (refl a)) (α @ refl (refl a))
    @ path_comp_assoc _ _ _
    @ path_comp_rid _
    @ (! path_comp_assoc _ _ _ @> α)
    @ (path_comp_lid _ @> α)
    @ (! path_comp_assoc _ _ _ @> α)
    @ (β <@ (path_comp_rinv _) @> α)
    @ ((path_comp_rid _) @> α)
  ).
  exact res.
Defined.

Theorem eckmann_hilton {X: ptype} (p q: Ω Ω X): p @ q = q @ p.
Proof.
  exact (! path_horzcomp_trans1 _ _ @ path_horzcomp_eq _ _
    @ path_horzcomp_trans2 _ _).
Defined.

(** ** Section 2.2: Functions are functors. *)

(** *** Map between fibrations over the same base. *)

Definition fibmap {A: UU} (P Q: fib A): UU := ∏ x: A, P x → Q x.

(** *** Composition of a section and a map of fibrations. *)

Definition fibcomp {A: UU} {P Q: fib A} (α: fibmap P Q) (f: sec P)
  : sec Q := λ x, α _ (f x).

(** *** Action of a map on a path (Lemma 2.2.1 from the book).
This is called [maponpaths] in UniMath. *)

Definition ap {A B: UU} (f: A → B) {x y: A} (p: x = y): f x = f y.
Proof.
  induction p.
  apply refl.
Defined.

Goal ∏ {A B: UU} (f: A → B) {x: A}, ap f (refl x) = refl (f x).
Proof.
  intros.
  apply refl.
Defined.

(** *** Action on path composition (part of Lemma 2.2.2 from the book). *)

Lemma ap_pathcomp {A B: UU} (f: A → B) {x y z: A} (p: x = y) (q: y = z)
  : ap f (p @ q) = ap f p @ ap f q.
Proof.
  induction p.
  induction q.
  apply refl.
Defined.

(** *** Action on path inversion (part of Lemma 2.2.2 from the book). *)

Lemma ap_pathinv {A B: UU} (f: A → B) {x y: A} (p: x = y)
  : ap f (! p) = ! ap f p.
Proof.
  induction p.
  apply refl.
Defined.

(** *** Action of map composition (part of Lemma 2.2.2 from the book). *)

Lemma ap_funcomp {A B C: UU} (f: A → B) (g: B → C) {x y: A} (p: x = y)
  : ap g (ap f p) = ap (g ∘ f) p.
Proof.
  induction p.
  apply refl.
Defined.

(** *** Actionf of the identity map (part of Lemma 2.2.2 from the book). *)

Lemma ap_funid {A: UU} {x y : A} (p: x = y): ap (fun_id A) p = p.
Proof.
  induction p.
  apply refl.
Defined.

(** ** Section 2.3: Type families are fibrations. *)

(** *** Transport over a fibration and along a path (Lemma 2.3.1 from the book).
This is also called _indiscernability of identicals_, and [transportf] on
UniMath. *)

Definition transport {A: UU} (P: fib A) {x y: A} (p: x = y): P x → P y.
Proof.
  induction p.
  apply fun_id.
Defined.

Notation "p #" := (transport _ p).

(** *** Transport over a constant fibration (Lemma 2.3.5 from the book). *)

Definition transport_fibconst {A B: UU} {x y: A} (p: x = y) (b: B)
  : transport (λ _, B) p b = b.
Proof.
  induction p.
  apply refl.
Defined.

(** *** Transport along a path composition (Lemma 2.3.9 from the book). *)

Lemma transport_pathcomp {A: UU} {P: fib A} {x y z : A}
  (p: x = y) (q: y = z) (u: P x)
  : (p @ q) # u = q # (p # u).
Proof.
  induction p.
  induction q.
  apply refl.
Defined.

(** *** Transport over a change of base (Lemma 2.3.10 from the book).*)

Lemma transport_basechange {A B: UU} (f: A → B) (P: fib B) {x y: A} (p: x = y)
  (u: P (f x))
  : transport (P ∘ f) p u = (transport P) (ap f p) u.
Proof.
  induction p.
  apply refl.
Defined.

(** *** Transport over a map of fibrations (Lemma 2.3.11 from the book).  *)

Lemma transport_fibmap {A: UU} {P Q: fib A} (f: fibmap P Q)
  {x y: A} (p: x = y) (u: P x)
  : transport Q p (f _ u) = f _ (transport P p u).
Proof.
  induction p.
  apply refl.
Defined.

(** *** Lift a path from the base to the total space of a fibration (Lemma
2.3.2 from the book). *)

Definition lift {A: UU} {P: fib A} {x y: A} (u: P x) (p: x = y)
  : (x ,, u) = (y ,,  p # u).
Proof.
  induction p.
  apply refl.
Defined.

Lemma lift_over {A: UU} {P: ∏ x: A, UU} {x y: A} (p: x = y) (u: P x)
  : ap pr1 (lift u p) = p.
Proof.
  induction p.
  apply refl.
Defined.

(** *** Action of a section of a fibration on a path (Lemma 2.3.4 from the
book). *)

Definition apd {A: UU} {P: fib A} {x y: A} (f: sec P) (p: x = y)
  : p # (f x) = f y.
Proof.
  induction p.
  apply refl.
Defined.

(** *** Action on path composition. *)

Lemma apd_pathcomp {A: UU} (P: fib A) {x y z: A} (f: sec P)
  (p: x = y) (q: y = z)
 : apd f (p @ q) = (transport_pathcomp p q (f x)) @ ap (q #) (apd f p) @ apd f q.
Proof.
  induction p.
  induction q.
  apply refl.
Defined.

(** *** Action of a section of a constant fibration (Lemma 2.3.8 from the
book). *)

Lemma apd_fibconst {A B: UU} {x y: A} (f: A → B) (p: x = y)
 : apd f p = transport_fibconst p (f x) @ ap f p.
Proof.
  induction p.
  apply refl.
Defined.

(** *** Action of a section of a fibration with a change of base. *)

Lemma apd_changebase {A B: UU} (f: A → B) (P: fib B) {x y: A} (g: sec P)
  (p: x = y)
  : apd (g ∘ f) p = transport_basechange f P p (g (f x)) @ apd g (ap f p).
Proof.
  induction p.
  apply refl.
Defined.

Lemma apd_fibmap {A: UU} {P Q: fib A} (g: fibmap P Q) (f: sec P) {x y: A} (p: x = y)
  : apd (fibcomp g f) p = transport_fibmap g p (f x) @ ap (g _) (apd f p).
Proof.
  induction p.
  apply refl.
Defined.

(** A variant of [apd] which builds the resulting path over the total space
instead of over the target fiber. *)

Definition apd_total2 {A: UU} {P: fib A} {x y: A} (f: sec P) (p: x = y)
  : (x,, f x) = (y,, f y).
Proof.
  pose (f' := λ x: A, (x,, f x)).
  exact (ap f' p).
Defined.

(** [apd_total2] is a combination of [lift] and [apd]. *)

Theorem apd_total2_transport {A: UU} {P: fib A} {x y: A} (f: sec P) (p: x = y)
  : apd_total2 f p =  lift (f x) p @ (ap (λ z, (y,, z)) (apd f p)).
Proof.
  induction p.
  apply refl.
Defined.

(** ** Section 2.4: Homotopies and equivalences *)

(** *** Definition of homotopy (Definition 2.4.1 from the book). *)

Definition homot {A: UU} {P: fib A} (f g: sec P): UU := ∏ x: A, f x = g x.

Notation "f ~ g" := (homot f g) (at level 70, no associativity): type_scope.

(** *** Homotopies are equivalence relations (Lemma 2.4.2 from the book). *)

Lemma homot_refl {A: UU} {P: fib A} (f: sec P): f ~ f.
Proof.
  intro x.
  apply refl.
Defined.

Lemma homot_symm {A: UU} {P: fib A} (f g: sec P): f ~ g → g ~ f.
Proof.
  intros h x.
  exact (! (h x)).
Defined.

Lemma homot_trans {A: UU} {P: fib A} (f g h: sec P): f ~ g → g ~ h → f ~ h.
Proof.
  intros h1 h2 x.
  exact ((h1 x) @ (h2 x)).
Defined.

(** *** Homotopies are natural transformations (Lemma 2.4.3 from the book).*)

Lemma homot_nat {A B : UU} {f g: A → B} (H: f ~ g) {x y : A} (p: x = y)
  : H x @ ap g p = ap f p @ H y.
Proof.
  induction p.
  change (ap f (refl x)) with (refl (f x)).
  change (ap g (refl x)) with (refl (g x)).
  exact ( path_comp_rid (H x) @ ! path_comp_lid (H x)).
Defined.

(** A corollary (Corollary 2.4.4 from the book).*)
Corollary homot_nat_cor {A:  UU} (f: A → A) (H: f ~ fun_id A) {x: A}
  : H (f x) = ap f (H x).
Proof.
  pose (h0 := homot_nat H (H x)).
  pose (h1 := (H (f x) <@ ! ap_funid (H x)) @ h0).
  pose (h2 := h1 @> (! (H x))).
  pose (l0 := ! path_comp_rid (H (f x))).
  pose (l1 := l0 @ (H (f x) <@ ! path_comp_rinv (H x)) @ path_comp_assoc _ _ _).
  pose (r0 := ! path_comp_rid (ap f (H x))).
  pose (r1 := r0 @ (ap f (H x) <@ ! path_comp_rinv (H x)) @ path_comp_assoc _ _ _).
  exact (l1 @ h2 @ ! r1).
Defined.

(** Variant of the corollary using rewrite. *)

Local Corollary homot_nat_cor' {A:  UU} (f: A → A) (H: f ~ fun_id A) {x: A}: H (f x) = ap f (H x).
Proof.
  pose (p := homot_nat H (H x) @> ! (H x)).
  cbn in p.
  rewrite ap_funid in p.
  do 2 rewrite <- path_comp_assoc in p.
  rewrite path_comp_rinv in p.
  do 2 rewrite path_comp_rid in p.
  exact p.
Defined.

(** *** Quasi-inverse of a function (Definition 2.4.6 from the book). *)

Definition qinv {A B: UU} (f: A → B)
  := ∑ g: B → A, (f ∘ g ~ fun_id B) × (g ∘ f ~ fun_id A) .

Definition qinv2fun {A B: UU} {f: A → B} (qinvf: qinv f) := pr1 qinvf.

Coercion qinv2fun: qinv >-> Funclass.

Definition qinv2proofr {A B: UU} {f: A → B} (qinvf: qinv f) :=  pr1 (pr2 qinvf).

Definition qinv2proofl {A B: UU} {f: A → B} (qinvf: qinv f) :=  pr2 (pr2 qinvf).

(** *** Quasi-inverse of identity and function composition. *)

Definition qinv_funid (A: UU): qinv (fun_id A) := (fun_id A,, refl,, refl).

Definition qinv_funcomp {A B C: UU} {f: A → B} {g: B → C}
  (fi: qinv f) (gi: qinv g)
  : qinv (g ∘ f).
Proof.
  exists (fi ∘ gi).
  split; intro x.
  - pose (α := ap g (qinv2proofr fi (gi x))).
    pose (β := qinv2proofr gi x).
    exact (α @ β).
  - pose (α := ap fi (qinv2proofl gi (f x))).
    pose (β := qinv2proofl fi x).
    exact (α @ β).
Defined.

(** *** Quasi-inverse of a quasi-inverse *)

Definition qinv_inv {A B: UU} {f: A → B} (g: qinv f): qinv g
  := (f,, (qinv2proofl g,, qinv2proofr g)).

(** *** Quasi-inverse of the path composition functions. *)

Definition qinv_pathcomp1 {A: UU} {x y: A} (p: x = y) (z: A)
  : qinv (λ q: y = z, p @ q).
Proof.
  exists (λ q, (!p) @ q).
  split; intro; cbn.
  - exact (path_comp_assoc _ _ _
            @ (path_comp_rinv _ @> x0) @ path_comp_lid _).
  - exact (path_comp_assoc _ _ _
            @ (path_comp_linv _ @> x0) @ path_comp_lid _).
Defined.

Definition qinv_pathcomp2 {A: UU} {x y: A} (p: x = y) (z: A)
  : qinv (λ q: z = x, q @ p).
Proof.
  exists (λ q, q @ (! p)).
  split; intro; cbn.
  - exact (! path_comp_assoc _ _ _
            @ (x0 <@ path_comp_linv _) @ path_comp_rid _).
  - exact (! path_comp_assoc _ _ _
            @ (x0 <@ path_comp_rinv _) @ path_comp_rid _).
Defined.

(** *** Quasi-inverse of the transport. *)

Definition qinv_transport {A: UU} (P: A → UU) {x y: A} (p: x = y)
  : qinv (transport P p).
Proof.
  exists (transport P (! p)).
  simpl.
  induction p.
  split ; intro; apply refl.
Defined.

(** Variant of the previous proof using previous lemmas instead of induction. *)

Local Definition qinv_transport' {A: UU} (P: A → UU) {x y: A} (p: x = y)
  : qinv (transport P p).
Proof.
  exists (transport P (! p)).
  split; cbn.
  - intro y0.
    pose (p1 := ! transport_pathcomp (! p) p y0).
    pose (p2 := ap (λ q: y = y, q # y0) (path_comp_linv p) ).
    exact (p1 @ p2).
  - intro x0.
    pose (p1 := ! transport_pathcomp p (! p) x0).
    pose (p2 := ap (λ q: x = x, q # x0) (path_comp_rinv p) ).
    exact (p1 @ p2).
Defined.

(** *** Property of a function being an equivalence. *)

Definition isequiv {A B: UU} (f: A → B)
  := (∑ g: B → A, f ∘ g ~ fun_id B) × (∑ h: B → A, h ∘ f ~ fun_id A).

(** *** A quasi-inverse induces an equivalence. *)

Lemma qinv2isequiv {A B: UU} {f: A → B} (finv: qinv f): isequiv f.
Proof.
  split.
  - exists finv.
    apply (qinv2proofr finv).
  - exists finv.
    apply (qinv2proofl finv).
Defined.

(** An equivalence induces a quasi-inverse. *)

Lemma isequiv2qinv {A B: UU} {f: A → B} (eq: isequiv f): qinv f.
Proof.
  induction eq as [ [g α] [h β] ].
  exists g.
  split.
  - apply α.
  - set (γ := λ x: B, ! β(g x) @ ap h (α x)).
    cbn in γ.
    intro x.
    exact (γ (f x) @ β x).
Defined.

Coercion isequiv2qinv: isequiv >-> qinv.

(** *** Being an equivalence is a property.
We will prove this later, after we introduce the relevant concepts. *)

Lemma isequiv_iscontr {A B: UU} (f: A → B) (e1 e2: isequiv f): e1 = e2.
Proof.
Abort.

(** *** Equivalence between types.
We also provide related projections, coercions and constructors. *)

Definition equiv (A B: UU) := ∑ f: A → B, isequiv f.

Notation "A ≃ B" := (equiv A B) (at level 80, no associativity).

Definition equiv2fun {A B: UU} (e: A ≃ B): A → B := pr1 e.

Definition equiv2isequiv {A B: UU} (e: A ≃ B): isequiv (pr1 e) := pr2 e.

Definition isequiv2equiv {A B: UU} {f: A → B} (eq: isequiv f): A ≃ B
  := (f,, eq).

Definition equiv2qinv {A B: UU} (e: A ≃ B): qinv (pr1 e)
  := isequiv2qinv (pr2 e).

Coercion equiv2isequiv: equiv >-> isequiv.

Definition qinv2equiv {A B: UU} {f: A → B} (g: qinv f): A ≃ B
  := (f,, qinv2isequiv g).

(** *** Equivalence between types is an equivalence relation (Lemma 2.4.12 from
the book). *)

Definition equiv_refl {A: UU}: A ≃ A := qinv2equiv (qinv_funid A).

Definition equiv_symm {A B: UU} (e: A ≃ B): B ≃ A
  := qinv2equiv (qinv_inv e).

Definition equiv_trans {A B C: UU} (e1: A ≃ B) (e2: B ≃ C): A ≃ C
  := qinv2equiv (qinv_funcomp e1 e2).

(** ** Section 2.6: Cartesian product types. *)

(** *** Paths between cartesian products (Theorem 2.6.2 from the book). *)

Definition prod_eq_proj {A B: UU} (x y: A × B)
  : x = y → (pr1 x = pr1 y) × (pr2 x = pr2 y)
  := λ p, ((ap pr1 p) ,, (ap (pr2: A × B → B) p)).

Definition prod_eq {A B: UU} (x y: A × B)
  : (pr1 x = pr1 y) × (pr2 x = pr2 y) → x = y.
Proof.
  induction x as [a b].
  induction y as [c d].
  cbn.
  intro p.
  induction p as [p1 p2].
  induction p1.
  induction p2.
  apply refl.
Defined.

Lemma prod_eq_qinv {A B: UU} {x y: A × B}: qinv (prod_eq_proj x y).
Proof.
  exists (prod_eq x y).
  split.
  - intro p.
    induction x as [a b].
    induction y as [c d].
    cbn in p.
    induction p as [p1 p2].
    induction p1.
    induction p2.
    apply refl.
  - intro p.
    induction p.
    induction x.
    apply refl.
Defined.

Definition prod_eq2 {A B: UU} {x x': A} {y y': B}
  : x = x' → y = y' → (x,, y) = (x',, y').
Proof.
  intros p1 p2.
  induction p1.
  induction p2.
  apply refl.
Defined.

Declare Scope path_scope.
Delimit Scope path_scope with path.
Bind Scope path_scope with path.

Notation "p1 × p2" := (prod_eq2 p1 p2): path_scope.

(** *** Other properties of paths over products. *)

Lemma path_prod_inv {A B: UU} {x x': A} {y y': B} (p: x = x') (q: y = y')
  : ! (p × q)%path = ((!p) × (!q))%path.
Proof.
  induction p.
  induction q.
  apply refl.
Defined.


(** *** Transport in a pointwise product of type families (Theorem 2.6.4 from
the book). *)

Definition transport_prod {Z: UU} (A B: Z → UU) {z w: Z} (p: z = w) (x: A z × B z):
   transport (λ z, A z × B z) p x = transport A p (pr1 x) ,, transport B p (pr2 x).
Proof.
  induction p.
  induction x.
  apply refl.
Defined.

Definition prod_fun {A B A' B': UU} (g: A → A') (h: B → B')
  : A × B → A' × B' := λ z, g (pr1 z) ,, h (pr2 z).

Notation "f × g" := (prod_fun f g): function_scope.

Definition ap_prod {A B A' B': UU} (g: A → A') (h: B → B') {x y: A × B}
                   (p: pr1 x = pr1 y) (q: pr2 x = pr2 y)
  : ap (g × h) (p × q)
    = prod_eq (prod_fun g h x) (prod_fun g h y) ( (ap g p) ,, (ap h q)).
Proof.
  induction x, y.
  cbn in p, q.
  induction p, q.
  apply refl.
Defined.

(** ** Section 2.7: Σ-types *)

Definition sum_eq_proj {A: UU} {P: A → UU} (w w': total2 P)
  : w = w' → ∑ p: pr1 w = pr1 w', p # (pr2 w) = pr2 w'.
Proof.
  intro e.
  induction e.
  exists (refl _).
  apply refl.
Defined.

Definition sum_eq {A: UU} {P: A → UU} {w w': total2 P}
  : (∑ p: pr1 w = pr1 w',  p # (pr2 w) = pr2 w') → w = w'.
Proof.
  intro X.
  induction X as [p q].
  induction w, w'.
  cbn in p.
  induction p.
  cbn in q.
  induction q.
  apply refl.
Defined.

Theorem sum_eq_qinv {A: UU} {P: A → UU} {w w': total2 P}: qinv (sum_eq_proj w w').
Proof.
  exists sum_eq.
  split ; intro.
  - induction w as [a b], w' as [a' b'].
    induction x as [p q].
    cbn in p.
    induction p.
    cbn in q.
    induction q.
    apply refl.
  - induction x.
    induction w as [a b].
    apply refl.
Defined.

(** Versione di sum_eq con migliori proprietà di type inference *)

Definition sum_eq' {A: UU} {P: A → UU} {a a': A} {b: P a} {b': P a'}
  : ∏ p: a = a', p # b = b' → (a,,b) = (a',,b')
  := λ p q, sum_eq(w:=a,,b)(w':=a',,b') (p ,, q).

Theorem sum_uniq {A: UU} {P: A → UU} (z: total2 P): z = (pr1 z ,, pr2 z).
Proof.
  induction z.
  apply sum_eq.
  cbn.
  exists (refl _).
  apply refl.
Defined.

Theorem transport_sum {A: UU} (P: A → UU) (Q: total2 P → UU) {x y: A}
                      (p: x = y) (u: P x) (z: Q (x ,, u))
  : transport (λ x, ∑ u: P x,  Q (x ,, u)) p (u ,, z)
    = (p # u ,, transport Q (sum_eq' p (refl (p # u))) z).
Proof.
  induction p.
  apply refl.
Defined.

(** ** Section 2.8: The unit type *)

Definition unit_eq (x y: unit): unit → (x = y).
Proof.
  intro.
  induction x, y.
  apply refl.
Defined.

Theorem unit_eq_equiv (x y: unit): (x = y) ≃ unit.
Proof.
  exists (λ _, tt).
  apply qinv_to_isequiv.
  exists (unit_eq x y).
  split.
  - intro z.
    unfold idfun, funcomp.
    induction z.
    apply refl.
  - intro z.
    induction z.
    unfold idfun, funcomp.
    induction x.
    apply refl.
Defined.

Theorem transport_unit {A: UU} {z w: A} (p: z = w) (x: unit):
  transport (λ z, unit) p x = x.
Proof.
  apply transportconst.
Defined.

(** ** Section 2.9: Π-types and the function extensionality axiom *)

Definition happly {A: UU} {P: A → UU} {f g: sec P}: (f = g) → (f ~ g).
Proof.
  intro p.
  induction p.
  intro.
  apply refl.
Defined.

Axiom funextAxiom: ∏ {A: UU} {P: A → UU} (f g: sec P), isequiv (@happly A P f g).

Definition funext {A: UU} {P: A → UU} {f g: sec P}: (f ~ g) → (f = g).
Proof.
  pose (ax := funextAxiom f g).
  apply isequiv_to_qinv in ax.
  exact ax.
Defined.

Lemma happly_funext {A: UU} {P: A → UU} (f g: sec P): happly ∘ funext ~ idfun (f ~ g).
Proof.
  set (ax := isequiv_to_qinv (funextAxiom f g)).
  exact (qinv_proof_r ax).
Defined.

Lemma funext_happly {A: UU} {P: A → UU} (f g: sec P): funext ∘ happly ~ idfun (f = g).
Proof.
  exact (qinv_proof_l (isequiv_to_qinv (funextAxiom f g))).
Defined.

Lemma funext_idpath {A: UU} {P: A → UU} (f: sec P): refl f = funext (λ x: A, refl (f x)).
Proof.
  change (λ x: A, refl (f x)) with (happly (refl f)).
  apply path_refl.
  apply funext_happly.
Defined.

Lemma funext_refl {A: UU} {P: A → UU} {f g: sec P} (α: f = g): ! α = funext (λ x, ! (happly α x)).
Proof.
  induction α.
  cbv - [funext].
  apply funext_idpath.  (* prende il posto di apply idapth perché usiamo un assioma *)
Defined.

Lemma funext_comp {A: UU} {P: A → UU} {f g h: sec P} (α: f = g) (β: g = h): α @ β  = funext (λ x, (happly α x) @ (happly β x)).
Proof.
  induction α.
  induction β.
  apply funext_idpath. (* prende il posto di apply idapth perché usiamo un assioma *)
Defined.

Lemma transport_fun {X: UU} {A B: X → UU} {x1 x2: X} (p: x1 = x2) (f: A x1 → B x1)
  : p # f = λ x: A x2, p # (f (! p # x)).
Proof.
  induction p.
  apply refl.
Defined.

(** Notare l'uso di tutti i ! in transport_fun'. Ciò è reso necessairio perché (p # !p # a)
è uguale ad a solo proposizionalmente *)

Lemma transport_fun' {X: UU} {A: X → UU} {B: ∏ x: X, (A x → UU)} {x1 x2: X} (p: x1 = x2) (f: ∏ a: A x1, B x1 a)
  : p # f = λ a: A x2, transport (λ w, B (pr1 w) (pr2 w)) (! sum_eq' (! p) (refl (! p # a))) (f (! p # a)).
Proof.
  induction p.
  apply refl.
Defined.

Lemma path_dep {X: UU} {A B: X → UU} {x y: X} (p: x = y) (f: A x → B x) (g: A y → B y):
  (transport (λ x, A x → B x) p f = g) ≃ ∏ a: A x, (p # (f a)) = g (p # a).
Proof.
  induction p.
  cbn.
  unfold idfun.
  exists happly.
  apply funextAxiom.
Defined.
