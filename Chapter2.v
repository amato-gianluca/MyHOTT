(** * Chapter 2 *)

Require Export Chapter1.

(** ** Reserved notations *)

Reserved Notation "X ≃ Y" (at level 80, no associativity).

(** ** Section 2.1: Types are higher groupoids *)

(* Lemma 2.1.1 with induction principle. *)
Local Definition paths_inv' {A: UU} {x y: A} (p: x = y): (y = x).
Proof.
  pose (D := λ (x y: A) (p: x = y), y = x).
  pose (d := (λ x: A, refl _) : ∏ x: A, D x x (refl _) ).
  exact (paths_rect_free D d x y p).
Defined.

(* Lemma 2.1.1 with tactics. *)
Definition paths_inv {A: UU} {x y: A} (p: x = y): y = x.
Proof.
  induction p.
  apply refl.
Defined.

Notation "! p" := (paths_inv p) (at level 50, left associativity).

(* Lemma 2.1.2 with induction principle. *)
Local Definition paths_comp' {A: UU} {x y z: A} (p: x = y) (q: y = z): x = z.
Proof.
  pose (D := λ (x y: A) (p: x = y), ∏ (z: A) (q: y = z), x = z).
  refine (paths_rect_free D _  x y p z q).
  unfold D.
  pose (E := λ (x y : A) (p: x = y), x = y).
  pose (e := λ (x: A), refl x).
  exact (paths_rect_free E e).
Defined.

(*
Lemma 2.1.2 with tactic.
*)
Definition paths_comp {A: UU} {x y z: A} (p: x = y) (q: y = z): x = z.
Proof.
  induction p.
  induction q.
  apply refl.
Defined.

Notation "p @ q" := (paths_comp p q) (at level 60, right associativity).

(* Begin Lemma 2.1.4. *)
Lemma paths_comp_lid {A: UU} {x y: A} (p: x = y): (refl _) @ p = p.
Proof.
  induction p.
  apply refl.
Defined.

Lemma paths_comp_rid{A: UU} {x y: A} (p: x = y): p @ (refl _) = p.
Proof.
  induction p.
  apply refl.
Defined.

Lemma paths_comp_rinv {A: UU} {x y: A} (p: x = y): p @ ! p = refl _.
Proof.
  induction p.
  apply refl.
Defined.

Lemma paths_comp_linv {A: UU} {x y: A} (p: x = y): !p @ p = refl _.
Proof.
  induction p.
  apply refl.
Defined.

Lemma paths_inv_inv {A: UU} {x y: A} (p: x = y): !(!p) = p.
Proof.
  induction p.
  apply refl.
Defined.

Lemma paths_comp_assoc {A: UU} {w x y z: A} (p: w = x) (q: x = y) (r: y = z)
  : p @ (q @ r) = (p @ q) @ r.
Proof.
  induction p.
  induction q.
  induction r.
  apply refl.
Defined.
(* End Lemma 2.1.4. *)

Definition paths_rwhisker {A: UU} {x y z: A} {p q: x = y} (α: p = q) (r: y = z)
  : p @ r = q @ r.
Proof.
  induction r.
  exact (paths_comp_rid _ @ α @ ! paths_comp_rid _).
Defined.

Notation "α @> q" := (paths_rwhisker α q) (at level 40).

(*
Version using induction without resorting to previous lemmas. There is
sometimes a choice between proving something by induction or resorting
to previous results.
*)

Local Definition paths_rwhisker' {A: UU} {x y z: A}
  {p q: x = y} (α: p = q) (r: y = z)
  : p @ r = q @ r.
Proof.
  induction r, q, α.
  apply refl.
Defined.

(*
The definiton of paths_lwhisker is simpler than paths_rwhisker due to the
asymmetry of paths_comp.
*)

Definition paths_lwhisker {A: UU} {x y z: A} {p q: x = y} (r: z = x) (α: p = q)
  : r @ p = r @ q.
Proof.
  induction r.
  exact (paths_comp_lid _ @ α @ ! paths_comp_lid _).
Defined.

Notation "p <@ α" := (paths_lwhisker p α) (at level 40).

Definition paths_horzcomp {A: UU} {x y z : A}
  {p q: x = y} {r s: y= z} (α: p = q) (β: r = s)
  : p @ r = q @ s := (α @> r) @ (q <@ β).

Notation "α ⋆ β" := (paths_horzcomp α β) (at level 40, left associativity).

Local Definition paths_horzcomp' {A: UU} {x y z : A}
  {p q: x =y} {r s : y= z} (α: p = q) (β: r = s)
  : p @ r = q @s := (p <@ β) @ (α @> s).

Local Notation "α ⋆' β" := (paths_horzcomp' α β)
  (at level 40, left associativity).

Local Lemma paths_horzcomp_eq  {A: UU} {x y z : A}
  {p q: x = y} {r s: y= z} (α: p = q) (β: r = s)
  : α ⋆ β = α ⋆' β.
Proof.
  induction α.
  induction β.
  induction p.
  induction r.
  apply refl.
Defined.

(**
Pointed type and loop space hierarchy. Here universe polymorphism of
ptype, Ω and fun_iter is essential. We define Ω as a function over
ptypes, as in the end of Section 2.1, instead of using the ad-hoc
definition in the middle of the same section.
*)

Definition ptype: UU := ∑ (A: UU), A.

Definition ptype_to_type: ptype → UU := pr1.

Coercion ptype_to_type: ptype >-> Sortclass.

Definition Ω (X: ptype): ptype := ((pr2 X = pr2 X) ,, refl (pr2 X)).

Goal Ω (Ω (nat,, 0)) =  (refl 0 = refl 0),, refl (refl 0).
Proof.
  apply refl.
Qed.

Notation "Ω² X" :=  (Ω (Ω X)) (at level 200).

(*
Due to the use of symmetric path_comp, this proof is quite convoluted. As an
example, this would be the proof using asymmetric paths_comp, due to the fact
that many equalities hold definitionally.

Proof.
  unfold "⋆".
  cbn.
  eapply paths_comp.
  - apply (! paths_comp_assoc _ _ _).
  - apply refl.
Defined
*)

Lemma paths_horzcomp_trans1 {A: UU} {a: A} (α: Ω² (A,, a)) (β: Ω² (A,, a))
  : α ⋆ β = α @ β.
Proof.
  unfold "⋆".
  simpl (pr2 (Ω (A,, a))) .
  change (α @> refl a) with (paths_comp_rid (refl a) @ α @ ! (paths_comp_rid (refl a))).
  change (refl a <@ β) with (paths_comp_lid (refl a) @ β @ ! (paths_comp_lid (refl a))).
  change (! paths_comp_lid (refl a)) with  (paths_comp_lid (refl a)).
  change (! paths_comp_rid (refl a)) with  (paths_comp_rid (refl a)).
  change (paths_comp_rid (refl a)) with (refl (refl a)).
  change (paths_comp_lid (refl a)) with (refl (refl a)).
  pose (res :=
    paths_comp_assoc (refl (refl a) @ α @ refl (refl a)) (refl (refl a)) (β @ refl (refl a))
    @ paths_comp_assoc _ _ _
    @ paths_comp_rid _
    @ (! paths_comp_assoc _ _ _ @> β)
    @ (paths_comp_lid _ @> β)
    @ (! paths_comp_assoc _ _ _ @> β)
    @ (α <@ (paths_comp_rinv _) @> β)
    @ ((paths_comp_rid _) @> β)
  ).
  exact res.
Defined.

Lemma paths_horzcomp_trans2 {A: UU} {a: A} (α: Ω² (A,, a)) (β: Ω²(A,, a))
  : α ⋆' β = β @ α.
Proof.
  (* We do all the changes in a single step. *)
  change ((refl (refl a) @ β @ refl (refl a)) @ refl (refl a) @ α @ refl (refl a) = β @ α).
  pose (res :=
    paths_comp_assoc (refl (refl a) @ β @ refl (refl a)) (refl (refl a)) (α @ refl (refl a))
    @ paths_comp_assoc _ _ _
    @ paths_comp_rid _
    @ (! paths_comp_assoc _ _ _ @> α)
    @ (paths_comp_lid _ @> α)
    @ (! paths_comp_assoc _ _ _ @> α)
    @ (β <@ (paths_comp_rinv _) @> α)
    @ ((paths_comp_rid _) @> α)
  ).
  exact res.
Defined.


Theorem eckmann_hilton {A: UU} {a: A} (p q: Ω² (A,, a)): p @ q = q @ p.
Proof.
  exact (! paths_horzcomp_trans1 _ _ @ paths_horzcomp_eq _ _
    @ paths_horzcomp_trans2 _ _).
Defined.

Lemma paths_horzcomp_comp {A: UU} {a b c d: A}
  {x: a = b} {y: a = b} (α: x = y) (p: b = c) (q: c = d)
  : paths_comp_assoc _ _ _ @ (α @> p @> q) =
    (α @> (p @ q)) @ paths_comp_assoc _ _ _.
Proof.
  induction q.
  induction p.
  induction α.
  induction x.
  apply refl.
Defined.

(** ** Section 2.2: Functions are functors *)

Definition ap {A B: UU} (f: A → B) {x y: A} (p: x = y): f x = f y.
Proof.
  induction p.
  apply refl.
Defined.

Lemma ap_pathscomp {A B: UU} (f: A → B) {x y z: A} (p: x=y) (q: y=z)
  : ap f (p @ q) = ap f p @ ap f q.
Proof.
  induction p.
  induction q.
  apply refl.
Defined.

Lemma ap_pathsinv {A B: UU} (f: A → B) {x y: A} (p: x=y)
  : ap f (! p) = ! ap f p.
Proof.
  induction p.
  apply refl.
Defined.

Lemma ap_funcomp {A B C: UU} (f: A → B) (g: B → C) {x y: A} (p: x = y)
  : ap g (ap f p) = ap (g ∘ f) p.
Proof.
  induction p.
  apply refl.
Defined.

Lemma ap_funid {A: UU} {x y : A} (p: x = y): ap (fun_id A) p = p.
Proof.
  induction p.
  apply refl.
Defined.

(** ** Section 2.3: Type families are fibrations *)

Definition transport {A: UU} (P: ∏ x: A, UU) {x y: A} (p: x = y): P x → P y.
Proof.
  induction p.
  apply fun_id.
Defined.

Notation "p #" := (transport _ p).

Definition lift {A: UU} {P: ∏ x: A, UU} {x y: A} (u: P x) (p: x = y)
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

Definition sec {A: UU} (P: A → UU): UU := ∏ x: A, P x.

Definition apd {A: UU} {P: ∏ x: A, UU} {x y: A} (f: sec P) (p: x = y)
  : p # (f x) = f y.
Proof.
  induction p.
  apply refl.
Defined.

(*
A variant of apd (action on path of a dependent familiy) which builds the
resulting path over the total space instead of over the target fiber.
*)
Definition apd_total2 {A: UU} {P: ∏ x: A, UU} {x y: A}
  (f: ∏ x: A, P x) (p: x = y)
  : (x,, f x) = (y,, f y).
Proof.
  pose (f' := λ x: A, (x,, f x)).
  exact (ap f' p).
Defined.

(* This proof that apd_total2 is a combination of lift and apd. *)

Theorem apd_total2_transport {A: UU} {P: ∏ x: A, UU} {x y: A}
  (f: sec P) (p: x = y)
  : apd_total2 f p =  lift (f x) p @ (ap (λ z, (y,, z)) (apd f p)).
Proof.
  induction p.
  apply refl.
Defined.

Definition transport_familyconst {A B: UU} {x y: A} (p: x = y) (b: B)
  : transport (λ _: A, B) p b = b.
Proof.
  induction p.
  apply refl.
Defined.

Lemma apd_const {A B: UU} {x y: A} (f: A → B) (p: x = y)
 : apd f p = transport_familyconst p (f x) @ ap f p.
Proof.
  induction p.
  apply refl.
Defined.

Lemma transport_pathscomp {A: UU} {P: ∏ x: A, UU} {x y z : A}
  (p: x = y) (q: y = z) (u: P x)
  : (p @ q) # u = q # (p # u).
Proof.
  induction p.
  induction q.
  apply refl.
Defined.

Lemma transport_familycomp {A B: UU}
  (f: A → B) (P: ∏ x: B, UU) {x y: A} (p: x = y)
  : transport (P ∘ f) p = (transport P) (ap f p).
Proof.
  induction p.
  apply refl.
Defined.

Lemma transport_pointfun {A: UU} {P Q: ∏ x: A, UU}
  (f: ∏ {x: A}, P x → Q x) {x y: A} (p: x = y) (u: P x)
  : p # (f u) = f (p # u).
Proof.
  induction p.
  apply refl.
Defined.

(** ** Section 2.4: Homotopies and equivalences *)

Definition homot {A: UU} {P: ∏ x: A, UU} (f g: sec P): UU := ∏ x: A, f x = g x.

Notation "f ~ g" := (homot f g) (at level 70, no associativity): type_scope.

Lemma homot_refl {A: UU} {P: ∏ x: A, UU} (f: sec P): f ~ f.
Proof.
  intro x.
  apply refl.
Defined.

Lemma homot_symm {A: UU} {P: ∏ x: A, UU} (f g: sec P): f ~ g → g ~ f.
Proof.
  intros h x.
  exact (! (h x)).
Defined.

Lemma homot_trans {A: UU} {P: ∏ x: A, UU} (f g h: sec P): f ~ g → g ~ h → f ~ h.
Proof.
  intros h1 h2 x.
  exact ((h1 x) @ (h2 x)).
Defined.

Lemma homot_nat {A B : UU} {f g: A → B} (H: f ~ g) {x y : A} (p: x = y)
  : H x @ ap g p = ap f p @ H y.
Proof.
  induction p.
  change (ap f (refl x)) with (refl (f x)).
  change (ap g (refl x)) with (refl (g x)).
  exact ( paths_comp_rid (H x) @ ! paths_comp_lid (H x)).
Defined.

(* without using rewrite *)

Corollary homot_nat_cor {A:  UU} (f: A → A) (H: f ~ fun_id A) {x: A}
  : H (f x) = ap f (H x).
Proof.
  pose (h0 := homot_nat H (H x)).
  pose (h1 := (H (f x) <@ ! ap_funid (H x)) @ h0).
  pose (h2 := h1 @> (! (H x))).
  pose (l0 := ! paths_comp_rid (H (f x))).
  pose (l1 := l0 @ (H (f x) <@ ! paths_comp_rinv (H x)) @ paths_comp_assoc _ _ _).
  pose (r0 := ! paths_comp_rid (ap f (H x))).
  pose (r1 := r0 @ (ap f (H x) <@ ! paths_comp_rinv (H x)) @ paths_comp_assoc _ _ _).
  exact (l1 @ h2 @ ! r1).
Defined.

(* using rewrite *)

Corollary homot_nat_cor' {A:  UU} (f: A → A) (H: f ~ fun_id A) {x: A}: H (f x) = ap f (H x).
Proof.
  pose (p := homot_nat H (H x) @> ! (H x)).
  cbn in p.
  rewrite ap_funid in p.
  do 2 rewrite <- paths_comp_assoc in p.
  rewrite paths_comp_rinv in p.
  do 2 rewrite paths_comp_rid in p.
  exact p.
Defined.

Definition qinv {A B: UU} (f: A → B)
  := ∑ g: B → A, (f ∘ g ~ fun_id B) × (g ∘ f ~ fun_id A) .

Definition qinv2fun {A B: UU} {f: A → B} (qinvf: qinv f) := pr1 qinvf.

Coercion qinv2fun: qinv >-> Funclass.

Definition qinv2proofr {A B: UU} {f: A → B} (qinvf: qinv f) :=  pr1 (pr2 qinvf).

Definition qinv2proofl {A B: UU} {f: A → B} (qinvf: qinv f) :=  pr2 (pr2 qinvf).

Definition qinv_funid (A: UU): qinv (fun_id A) := (fun_id A,, refl,, refl).

Definition qinv_pathscomp1 {A: UU} {x y: A} (p: x = y) (z: A)
  : qinv (λ q: y = z, p @ q).
Proof.
  exists (λ q, (!p) @ q).
  split; intro; cbn.
  - exact (paths_comp_assoc _ _ _
            @ (paths_comp_rinv _ @> x0) @ paths_comp_lid _).
  - exact (paths_comp_assoc _ _ _
            @ (paths_comp_linv _ @> x0) @ paths_comp_lid _).
Defined.

Definition qinv_pathscomp2 {A: UU} {x y: A} (p: x = y) (z: A)
  : qinv (λ q: z = x, q @ p).
Proof.
  exists (λ q, q @ (! p)).
  split; intro; cbn.
  - exact (! paths_comp_assoc _ _ _
            @ (x0 <@ paths_comp_linv _) @ paths_comp_rid _).
  - exact (! paths_comp_assoc _ _ _
            @ (x0 <@ paths_comp_rinv _) @ paths_comp_rid _).
Defined.

Definition qinv_transport {A: UU} (P: A → UU) {x y: A} (p: x = y)
  : qinv (transport P p).
Proof.
  exists (transport P (! p)).
  simpl.
  induction p.
  split ; intro; apply refl.
Defined.

(* Vatiant of the proof using previous lemmas instead of induction *)
Local Definition qinv_transport' {A: UU} (P: A → UU) {x y: A} (p: x = y)
  : qinv (transport P p).
Proof.
  exists (transport P (! p)).
  split; cbn.
  - intro y0.
    pose (p1 := ! transport_pathscomp (! p) p y0).
    pose (p2 := ap (λ q: y = y, q # y0) (paths_comp_linv p) ).
    exact (p1 @ p2).
  - intro x0.
    pose (p1 := ! transport_pathscomp p (! p) x0).
    pose (p2 := ap (λ q: x = x, q # x0) (paths_comp_rinv p) ).
    exact (p1 @ p2).
Defined.

Definition isequiv {A B: UU} (f: A → B)
  := (∑ g: B → A, f ∘ g ~ fun_id B) × (∑ h: B → A, h ∘ f ~ fun_id A).

Lemma qinv2isequiv {A B: UU} {f: A → B} (finv: qinv f): isequiv f.
Proof.
  split.
  - exists finv.
    apply (qinv2proofr finv).
  - exists finv.
    apply (qinv2proofl finv).
Defined.

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

(* To be proved later *)

Lemma isequiv_iscontr {A B: UU} (f: A → B) (e1 e2: isequiv f): e1 = e2.
Proof.
Abort.

Definition equiv (A B: UU) := ∑ f: A → B, isequiv f.

Notation "A ≃ B" := (equiv A B).

Definition equiv2fun {A B: UU} (e: A ≃ B): A → B := pr1 e.

Definition equiv2isequiv {A B: UU} (e: A ≃ B): isequiv (pr1 e) := pr2 e.

Definition isequiv2equiv {A B: UU} {f: A → B} (eq: isequiv f): A ≃ B
  := (f,, eq).

Definition equiv2qinv {A B: UU} (e: A ≃ B): qinv (pr1 e)
  := isequiv2qinv (pr2 e).

Coercion equiv2isequiv: equiv >-> isequiv.

Definition qinv2equiv {A B: UU} {f: A → B} (g: qinv f): A ≃ B
  := (f,, qinv2isequiv g).

Definition equiv_refl {A: UU}: A ≃ A := qinv2equiv (qinv_funid A).

Definition qinv_inv {A B: UU} {f: A → B} (g: qinv f): qinv g
  := (f,, (qinv2proofl g,, qinv2proofr g)).

Definition equiv_symm {A B: UU} (e: A ≃ B): B ≃ A
  := qinv2equiv (qinv_inv e).

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

Definition equiv_trans {A B C: UU} (e1: A ≃ B) (e2: B ≃ C): A ≃ C
  := qinv2equiv (qinv_funcomp e1 e2).

(** ** Section 2.6: Cartesian product types *)

Definition prod_eq_proj {A B: UU} (x y: A × B)
  : x = y → (pr1 x = pr1 y) × (pr2 x = pr2 y)
  := λ p, ((ap pr1 p) ,, (ap prod_pr2 p)).

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

Notation "p1 × p2" := (prod_eq _ _ (p1 ,, p2)): paths_scope.

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
  apply paths_refl.
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

Lemma paths_dep {X: UU} {A B: X → UU} {x y: X} (p: x = y) (f: A x → B x) (g: A y → B y):
  (transport (λ x, A x → B x) p f = g) ≃ ∏ a: A x, (p # (f a)) = g (p # a).
Proof.
  induction p.
  cbn.
  unfold idfun.
  exists happly.
  apply funextAxiom.
Defined.
