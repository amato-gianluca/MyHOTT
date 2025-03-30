(** * Chapter 2 *)

Require Export MyHOTT.Chapter1.

(** ** Reserved notations *)

Reserved Notation "p @ q" (at level 60, right associativity).
Reserved Notation "! p" (at level 50, left associativity).
Reserved Notation "p # x" (at level 60, no associativity).
Reserved Notation "f ~ g" (at level 70, no associativity).
Reserved Notation "X ≃ Y" (at level 80, no associativity).


(** ** Section 2.1: Types are higher groupoids *)

(* Lemma 2.1.1 con principio di induzione *)
Lemma paths_refl' : ∏ {A: UU} {x y: A}, (x = y) → (y = x).
Proof.
  intro A.
  pose (D := λ (x y: A) (p: x = y), y = x).
  pose (d := (λ x: A, idpath x) : ∏ x: A, D x x (idpath x) ).
  exact (paths_rect_gen D d).
Defined.

(* Lemma 2.1.1 con tattiche *)
Lemma paths_refl: ∏ {A: UU} {x y: A}, (x = y) → (y = x).
Proof.
  intros A x y p.
  induction p.
  apply idpath.
Defined.

Notation "! p" := (paths_refl p).

(* Lemma 2.1.2 con induzione *)
Lemma paths_trans':  ∏ {A: UU} {x y z: A}, x = y → y = z → x = z.
Proof.
  intro A.
  pose (D := λ (x y: A) (p: x = y), ∏ (z: A) (q: y = z), x = z).
  pose (d := (λ (x: A) (z: A) (q: x = z), q) : ∏ x: A,  D x x (idpath x)).
  intros x y z p.
  exact (paths_rect_gen D d x y p z).
Defined.

(* Lemma 2.1.2 con tattiche *)
Lemma paths_trans:  ∏ {A: UU} {x y z: A}, x = y → y=z → x=z.
Proof.
  intros A x y z p q.
  induction p.
  exact q.
Defined.

Notation "p @ q" := (paths_trans p q).

(* Lemma 2.1.4 *)

Lemma paths_trans_lid: ∏ {A: UU} {x y: A} (p: x = y), (idpath x) @ p = p.
Proof. reflexivity. Defined.

Lemma paths_trans_rid: ∏ {A: UU} {x y: A} (p: x = y), p @ (idpath y) = p.
Proof.
  intros.
  induction p.
  apply idpath.
Defined.

Lemma paths_trans_refl1: ∏ {A: UU} {x y: A} (p: x = y), p @ ! p = idpath x.
Proof.
  intros.
  induction p.
  apply idpath.
Defined.

Lemma paths_trans_refl2: ∏ {A: UU} {x y: A} (p: x = y), !p @ p = idpath y.
Proof.
  intros.
  induction p.
  apply idpath.
Defined.

Lemma paths_refl_refl: ∏ {A: UU} {x y: A} (p: x = y), !(!p) = p.
Proof.
  intros.
  induction p.
  apply idpath.
Defined.

Lemma paths_trans_assoc: ∏ {A: UU} {w x y z: A} (p: w = x) (q: x = y) (r: y = z), p @ (q @ r) = (p@ q) @ r.
Proof.
  intros.
  induction p.
  apply idpath.
Defined.

Definition Ω {A: UU} (a: A) := a = a.

Definition Ωsquare {A: UU} (a: A) := idpath a = idpath a.

Notation "Ω²" := Ωsquare.

Definition paths_right_whisker {A: UU} {x y z: A} {p q: x = y} (α: p = q) (r: y = z)
  : (p @ r) = (q @ r).
Proof.
  induction r.
  exact (paths_trans_rid p @ α @ ! (paths_trans_rid q)).
Defined.

Notation "α @> q" := (paths_right_whisker α q) (at level 40).

Definition paths_left_whisker {A: UU} {x y z: A} {p q: x = y}(r: z = x) (α: p = q) : (r @ p ) = (r @ q).
Proof.
  induction r.
  exact α.
Defined.

Notation "p <@ α" := (paths_left_whisker p α) (at level 40).

Definition horz_comp {A: UU} {x y z : A} {p q: x =y} {r s : y= z} (α: p = q) (β: r = s)
  : (p@r) = (q@s)  :=  (α @> r) @ (q <@ β).

Notation "α ⋆ β" := (horz_comp α β) (at level 40, left associativity).

Definition horz_comp' {A: UU} {x y z : A} {p q: x =y} {r s : y= z} (α: p = q) (β: r = s)
  : (p@r) = (q@s) := (p <@ β) @ (α @> s).

Notation "α ⋆' β" := (horz_comp' α β) (at level 40, left associativity).

Lemma horz_comp_eq  {A: UU} {x y z : A} {p q: x =y} {r s : y= z} (α: p = q) (β: r = s)
  : α ⋆ β = α ⋆' β.
Proof.
  induction α.
  induction β.
  induction p.
  induction r.
  apply idpath.
Defined.

Lemma horz_comp_trans1 {A: UU} {a: A} (α: Ω² a) (β: Ω² a)
  : α ⋆ β = α @ β.
Proof.
  unfold "⋆".
  cbn.
  rewrite paths_trans_rid.
  apply idpath.
Defined.

Lemma horz_comp_trans2 {A: UU} {a: A} (α: Ω² a) (β: Ω² a)
  : horz_comp' α β = β @ α.
Proof.
  unfold "⋆'".
  cbn.
  rewrite paths_trans_rid.
  apply idpath.
Defined.

Theorem eckmann_hilton {A: UU} {a: A} (p q: Ω² a): p @ q = q @ p.
Proof.
  exact (! horz_comp_trans1 p q @ horz_comp_eq p q @ horz_comp_trans2 p q).
Defined.

(** ** Section 2.2: Functions are functors *)

Definition ap {A B: UU} (f: A → B) {x y: A} (p: x = y): f x = f y.
Proof.
  induction p.
  apply idpath.
Defined.

Lemma ap_trans {A B: UU} (f: A → B) {x y z: A}  (p: x=y) (q: y=z)
  : ap f (p @ q) = ap f p @ ap f q.
Proof.
  induction p.
  apply idpath.
Defined.

Lemma ap_refl {A B: UU} (f: A → B) {x y: A} (p: x=y)
  : ap f (! p) = ! ap f p.
Proof.
  induction p.
  apply idpath.
Defined.

Lemma ap_funcomp {A B C: UU} (f: A → B) (g: B → C) {x y: A} (p: x = y)
  : ap g (ap f p) = ap (g ∘ f) p.
Proof.
  induction p.
  apply idpath.
Defined.

Lemma ap_idfun {A: UU} {x y : A} (p: x=y): ap (idfun A) p = p.
Proof.
  induction p.
  apply idpath.
Defined.

(** ** Section 2.3: Type families are fibrations *)

Section TypeFamilies.

Definition transport {A: UU} (P: ∏ x: A, UU) {x y: A} (p: x = y): P x → P y.
Proof.
  induction p.
  apply idfun.
Defined.

Notation "p #" := (transport _ p).

Definition lift {A: UU} {P: ∏ x: A, UU} {x y: A} (u: P x) (p: x = y)
  : (x ,, u) = (y ,,  p # u).
Proof.
  induction p.
  apply idpath.
Defined.

Lemma lift_over {A: UU} {P: ∏ x: A, UU} {x y: A} (p: x = y) (u: P x)
  : ap pr1 (lift u p) = p.
Proof.
  induction p.
  apply idpath.
Defined.

Definition apd {A: UU} {P: ∏ x: A, UU} {x y: A} (f: ∏ x: A, P x) (p: x = y)
  : p # (f x) = f y.
Proof.
  induction p.
  apply idpath.
Defined.

Definition transportconst {A B: UU} {x y: A} (p: x = y) (b: B)
  : transport (λ _: A, B) p b = b.
Proof.
  induction p.
  apply idpath.
Defined.

Lemma apd_transport {A B: UU} {x y: A} (f: A → B) (p: x = y)
 : apd f p = transportconst p (f x) @ ap f p.
Proof.
  induction p.
  apply idpath.
Defined.

Lemma transport_trans {A: UU} {P: ∏ x: A, UU} {x y z : A} (p: x = y) (q: y = z) (u: P x)
  : q # (p # u) = (p @ q) # u.
Proof.
  induction p.
  apply idpath.
Defined.

Lemma transport_funcomp {A B: UU} (f: A → B) (P: ∏ x: B, UU) {x y: A} (p: x = y):
  transport (P ∘ f) p = (transport P) (ap f p).
Proof.
  induction p.
  apply idpath.
Defined.

Lemma transport_funfamily {A: UU} {P Q: ∏ x: A, UU} (f: ∏ x: A, P x → Q x) {x y: A} (p: x = y) (u: P x):
  p # (f x u) = f y (p # u).
Proof.
  induction p.
  apply idpath.
Defined.

(** ** Section 2.4: Homotopies and equivalences *)

Section Homotopies.

Definition sec {A: UU} (P: A → UU): UU := ∏ x: A, P x.

Definition homot {A: UU} {P: ∏ x: A, UU} (f g: sec P): UU := ∏ x: A, f x = g x.

Notation "f ~ g" := (homot f g): type_scope.

Lemma homot_refl {A: UU} {P: ∏ x: A, UU} (f: sec P): f ~ f.
Proof.
  intro x.
  apply idpath.
Defined.

Lemma homot_symm {A: UU} {P: ∏ x: A, UU}(f g: sec P): f ~ g → g ~ f.
Proof.
  intros h x.
  exact (! (h x)).
Defined.

Lemma homot_trans {A: UU} {P: ∏ x: A, UU}(f g h: sec P): f ~ g → g ~ h → f ~ h.
Proof.
  intros h1 h2 x.
  exact ((h1 x) @ (h2 x)).
Defined.

Lemma homot_nat {A B : UU} {f g: A → B} (H: f ~ g) {x y : A} (p: x = y): H x @ ap g p = ap f p @ H y.
Proof.
  induction p.
  cbn.
  apply paths_trans_rid.
Defined.

(* without using rewrite *)

Corollary homot_nat_cor {A:  UU} (f: A → A) (H: f ~ idfun A) {x: A}: H (f x) = ap f (H x).
Proof.
  eapply paths_trans.
  apply paths_refl.
  apply paths_trans_rid.
  unfold idfun.
  eapply paths_trans.
  apply paths_refl.
  apply (ap _ (paths_trans_refl1 (H x))).
  eapply paths_trans.
  apply paths_trans_assoc.
  apply (paths_trans(y:= (ap f (H x) @ H x) @  ! H x)).
  {
    apply (ap (λ z, z @ ! H x)).
    eapply paths_trans.
    apply paths_refl.
    apply (ap _ (ap_idfun (H x))).
    apply (homot_nat H).
  }
  eapply paths_trans.
  apply paths_refl.
  apply paths_trans_assoc.
  eapply paths_trans.
  apply (ap _ (paths_trans_refl1 _)).
  apply paths_trans_rid.
Defined.

(* using rewrite *)

Corollary homot_nat_cor' {A:  UU} (f: A → A) (H: f ~ idfun A) {x: A}: H (f x) = ap f (H x).
Proof.
  pose (p := homot_nat H (H x)).
  change (idfun A x) with x in p.
  rewrite ap_idfun in p.
  pose (p' := p @> (! (H x))).
  do 2 rewrite <- paths_trans_assoc in p'.
  do 2 rewrite paths_trans_refl1 in p'.
  do 2 rewrite paths_trans_rid in p'.
  exact p'.
Defined.

Definition qinv {A B: UU} (f: A → B) := ∑ g: B → A, (f ∘ g ~ idfun B) × (g ∘ f ~ idfun A) .

Definition qinv_to_fun {A B: UU} {f: A → B} (qinvf: qinv f) := pr1 qinvf.

Definition qinv_proof_r {A B: UU} {f: A → B} (qinvf: qinv f) :=  pr1 (pr2 qinvf).

Definition qinv_proof_l {A B: UU} {f: A → B} (qinvf: qinv f) :=  pr2 (pr2 qinvf).

Coercion qinv_to_fun: qinv >-> Funclass.

Definition qinv_idfun {A: UU}: qinv (idfun A).
Proof.
  exists (idfun A).
  split; intro; apply idpath.
Defined.

Definition qinv_paths_trans1 {A: UU} {x y: A} (p: x=y) (z: A): qinv (λ z: y=z, p @ z).
Proof.
  exists (λ z, (!p) @ z).
  induction p.
  split ; intro ; apply idpath.
Defined.

Definition qinv_paths_trans2 {A: UU} {x y: A} (p: x=y) (z: A): qinv (λ z: z=x, z @ p).
Proof.
  exists (λ z, z @ (! p)).
  split ; intro ; unfold "∘".
  - rewrite <- paths_trans_assoc.
    rewrite paths_trans_refl2.
    apply paths_trans_rid.
  - rewrite <- paths_trans_assoc.
    rewrite paths_trans_refl1.
    apply paths_trans_rid.
Defined.

Definition qinv_transport {A: UU} (P: A → UU) {x y: A} (p: x=y): qinv (transport P p).
Proof.
  exists (transport P (! p)).
  induction p.
  split ; intro; apply idpath.
Defined.

Definition isequiv {A B: UU} (f: A → B)
  := (∑ g: B → A, f ∘ g ~ idfun B) × (∑ h: B → A, h ∘ f ~ idfun A).

Lemma qinv_to_isequiv {A B: UU} {f: A → B} (qinvf: qinv f): isequiv f.
Proof.
  split.
  - exists qinvf.
    apply (qinv_proof_r qinvf).
  - exists qinvf.
    apply (qinv_proof_l qinvf).
Defined.

Lemma isequiv_to_qinv {A B: UU} {f: A → B} (eq: isequiv f): qinv f.
Proof.
  induction eq as [ [g α] [h β] ].
  exists g.
  split.
  - apply α.
  - set (γ := λ x: B, ! β(g x) @ ap h (α x)).
    unfold idfun in γ.
    intro x.
    unfold idfun.
    exact (γ (f x) @ β x).
Defined.

(* To be proved later *)

Lemma isequiv_iscontr {A B: UU} (f: A → B) (e1 e2: isequiv f): e1 = e2.
Proof.
Abort.

Lemma isequiv_idfun (A: UU): isequiv (idfun A).
Proof.
  apply qinv_to_isequiv.
  apply qinv_idfun.
Defined.

Lemma isequiv_comp {A B C: UU} {f: A → B} {g: B → C} (e1: isequiv f) (e2: isequiv g): isequiv (g ∘ f).
Proof.
  apply qinv_to_isequiv.
  apply isequiv_to_qinv in e1.
  apply isequiv_to_qinv in e2.
  exists (e1 ∘ e2).
  split ; intro x.
  - pose (α := ap g (qinv_proof_r e1 (e2 x))).
    pose (β := qinv_proof_r e2 x).
    exact (α @ β).
  - pose (α := ap e1 (qinv_proof_l e2 (f x))).
    pose (β := qinv_proof_l e1 x).
    exact (α @ β).
Defined.

Definition equiv (A B: UU) := ∑ f: A → B, isequiv f.

Notation "A ≃ B" := (equiv A B).

Lemma equiv_refl {A: UU}: A ≃ A.
Proof.
  exists (idfun A).
  apply isequiv_idfun.
Defined.

Lemma isequiv_symm {A B: UU} (e: A ≃ B): B ≃ A.
Proof.
  induction e as [f finv].
  apply isequiv_to_qinv in finv.
  exists finv.
  apply qinv_to_isequiv.
  exists f.
  split.
  - apply (qinv_proof_l finv).
  - apply (qinv_proof_r finv).
Defined.

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
  apply idpath.
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
    apply idpath.
  - intro p.
    induction p.
    induction x.
    apply idpath.
Defined.

Definition transport_prod {Z: UU} (A B: Z → UU) {z w: Z} (p: z = w) (x: A z × B z):
   transport (λ z, A z × B z) p x = transport A p (pr1 x) ,, transport B p (pr2 x).
Proof.
  induction p.
  induction x.
  apply idpath.
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
  apply idpath.
Defined.

(** ** Section 2.7: Σ-types *)

Definition sum_eq_proj {A: UU} {P: A → UU} (w w': total2 P)
  : w = w' → ∑ p: pr1 w = pr1 w', p # (pr2 w) = pr2 w'.
Proof.
  intro e.
  induction e.
  exists (idpath _).
  apply idpath.
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
  apply idpath.
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
    apply idpath.
  - induction x.
    induction w as [a b].
    apply idpath.
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
  exists (idpath _).
  apply idpath.
Defined.

Theorem transport_sum {A: UU} (P: A → UU) (Q: total2 P → UU) {x y: A}
                      (p: x = y) (u: P x) (z: Q (x ,, u))
  : transport (λ x, ∑ u: P x,  Q (x ,, u)) p (u ,, z)
    = (p # u ,, transport Q (sum_eq' p (idpath (p # u))) z).
Proof.
  induction p.
  apply idpath.
Defined.

(** ** Section 2.8: The unit type *)

Definition unit_eq (x y: unit): unit → (x = y).
Proof.
  intro.
  induction x, y.
  apply idpath.
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
    apply idpath.
  - intro z.
    induction z.
    unfold idfun, funcomp.
    induction x.
    apply idpath.
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
  apply idpath.
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

Lemma funext_idpath {A: UU} {P: A → UU} (f: sec P): idpath f = funext (λ x: A, idpath (f x)).
Proof.
  change (λ x: A, idpath (f x)) with (happly (idpath f)).
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
  apply idpath.
Defined.

(** Notare l'uso di tutti i ! in transport_fun'. Ciò è reso necessairio perché (p # !p # a)
è uguale ad a solo proposizionalmente *)

Lemma transport_fun' {X: UU} {A: X → UU} {B: ∏ x: X, (A x → UU)} {x1 x2: X} (p: x1 = x2) (f: ∏ a: A x1, B x1 a)
  : p # f = λ a: A x2, transport (λ w, B (pr1 w) (pr2 w)) (! sum_eq' (! p) (idpath (! p # a))) (f (! p # a)).
Proof.
  induction p.
  apply idpath.
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
