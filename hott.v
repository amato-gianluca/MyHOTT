Require Import UniMath.Foundations.Preamble.

Definition idfun (A: UU): A → A := λ x: A, x.

Definition funcomp {A B C: UU} (f: B → C) (g: A → B): A → C := λ x: A, f (g x).

Notation "f ∘ g" := (funcomp f g).

Definition dirprod (A B: UU): UU :=  ∑ (_: A),  B.

Notation "A × B" := (dirprod A B).

Definition prod_pr1 {A B: UU}: A × B → A := pr1.

Definition prod_pr2 {A B: UU}: A × B → B := pr2.

Definition sec {A: UU} (P: A → UU): UU := ∏ x: A, P x.

Lemma paths_rect_gen : ∏ {A : UU} (P : ∏ x y : A, x = y → UU) (refl: ∏ (x: A), P x x (idpath x)),
  ∏ (x y: A) (p : x = y), P x y p.
Proof.
  intros A P refl x.
  exact (paths_rect A x (P x) (refl x)).
Defined. 

Lemma paths_rect_gen_simpl: ∏ {A : UU} (P : ∏ x y : A, x = y → UU) (refl: ∏ (x: A), P x x (idpath x)),
  ∏ (x: A), paths_rect_gen P refl x x (idpath x) = refl x.
Proof. reflexivity. Defined.
  
(* Lemma 2.1.1 con principio di induzione *)
Lemma paths_refl1 : ∏ {A: UU} {x y: A}, (x = y) → (y = x).
Proof.
  intro A.
  pose (D := λ (x y: A) (p: x = y), y = x).
  pose (d := (λ x: A, idpath x) : ∏ x: A, D x x (idpath x) ). 
  exact (paths_rect_gen D d).
Defined.

(* Lemma 2.1.1 con tattiche *)
Lemma paths_refl2: ∏ {A: UU} {x y: A}, (x = y) → (y = x).
Proof.
  intros A x y p.
  induction p.
  apply idpath.
Defined.

Notation "! p" := (paths_refl2 p).

(* Lemma 2.1.2 con induzione *)
Lemma paths_trans1:  ∏ {A: UU} {x y z: A}, x = y → y=z → x=z.
Proof.
  intro A.
  pose (D := λ (x y: A) (p: x = y), ∏ (z: A) (q: y =z), x = z).
  pose (d := (λ (x: A) (z: A) (q: x = z), q) : ∏ x: A,  D x x (idpath x)).
  intros x y z p.
  exact ((paths_rect_gen D d x y p) z).
Defined.

(* Lemma 2.1.2 con tattiche *)
Lemma paths_trans2:  ∏ {A: UU} {x y z: A}, x = y → y=z → x=z.
Proof.
  intros A x y z p q.
  induction p.
  exact q.
Defined.

Notation "p ; q" := (paths_trans2 p q) (at level 60).

(* Lemma 2.1.4 *)

Lemma paths_trans_lid: ∏ {A: UU} {x y: A} (p: x = y), (idpath x) ; p = p.
Proof. reflexivity. Defined.

Lemma paths_trans_rid: ∏ {A: UU} {x y: A} (p: x = y), p ; (idpath y) = p.
Proof.
  intros.
  induction p.
  apply idpath.
Defined.

Lemma paths_tran_refl1: ∏ {A: UU} {x y: A} (p: x = y), p ; ! p = idpath x.
Proof.
  intros.
  induction p.
  apply idpath.
Defined.

Lemma paths_tran_refl2: ∏ {A: UU} {x y: A} (p: x = y), !p ; p = idpath y.
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

Lemma paths_trans_assoc: ∏ {A: UU} {w x y z: A} (p: w = x) (q: x = y) (r: y = z), p ; (q ; r) = (p; q) ; r.
Proof.
  intros.
  induction p.
  apply idpath.
Defined.


Definition Ω (A: UU) (a: A) := a = a.

Definition Ω2 (A: UU) (a: A) := idpath a = idpath a.

Definition ru {A: UU} {x y: A} (p: x = y): p = p ; idpath y := ! paths_trans_rid p.

Definition lu {A: UU} {x y: A} (p: x = y): p = idpath x ; p := idpath p.

Definition right_whisker {A: UU} {x y z: A} {p q: x = y} (α: p = q) (r: y = z) : (p ; r) = (q ; r).
Proof.
  induction r.
  exact (! ru p ; α ; ru q).
Defined.

Definition left_whisker {A: UU} {x y z: A} {p q: x = y}(r: z = x) (α: p = q) : (r ; p ) = (r ; q).
Proof.
  induction r.
  exact α.
Defined.

Definition horz_comp1 {A: UU} {x y z : A} {p q: x =y} {r s : y= z} (α: p = q) (β: r = s): (p;r) = (q; s) 
  := (right_whisker α r) ; (left_whisker q β).

Definition horz_comp2 {A: UU} {x y z : A} {p q: x =y} {r s : y= z} (α: p = q) (β: r = s): (p;r) = (q; s) 
  := (left_whisker p β) ; (right_whisker α s).

Lemma horz_comp_eq  {A: UU} {x y z : A} {p q: x =y} {r s : y= z} (α: p = q) (β: r = s): horz_comp1 α β = horz_comp2 α β.
Proof.
  induction α.
  induction β.
  induction p.
  induction r.
  apply idpath.
Defined.


Lemma horz_comp_trans1 {A: UU} {a: A} (α: idpath a = idpath a) (β: idpath a = idpath a): horz_comp1 α β = α ; β.
Proof.
  unfold horz_comp1.
  unfold right_whisker.
  cbn - [left_whisker].
  unfold left_whisker.
  cbn.
  rewrite paths_trans_rid.
  apply idpath.
Defined.

Lemma horz_comp_trans2 {A: UU} {a: A} (α: idpath a = idpath a) (β: idpath a = idpath a): horz_comp2 α β = β ; α.
Proof.
  unfold horz_comp2.
  cbn.
  rewrite paths_trans_rid.
  apply idpath.
Defined.

Theorem eckmann_hilton {A: UU} {a: A} (p q: Ω2 A a): p ; q = q ; p.
Proof.
  rewrite <- horz_comp_trans1.
  rewrite <- horz_comp_trans2.
  apply (horz_comp_eq p q).
Defined. 

Definition ap {A B: UU} {x y: A} (f: A → B) (p: x = y): f x = f y.
Proof.
  induction p.
  apply idpath.
Defined.

Lemma ap_idfun (A: UU) {x y : A} (p: x=y): ap (idfun A) p = p.
Proof.
  induction p.
  apply idpath.
Defined.

Definition transport {A: UU} (P: ∏ x: A, UU) {x y: A} (p: x = y): P x → P y.
Proof.
  induction p.
  apply idfun.
Defined.

Notation "p #" := (transport _ p) (at level 60).

Definition lift {A: UU} {P: ∏ x: A, UU} {x y: A} (u: P x) (p: x = y): (x ,, u) = (y ,,  p # u).
Proof.
  induction p.
  apply idpath.
Defined.

Lemma lift_over {A: UU} {P: ∏ x: A, UU} {x y: A} (p: x = y) (u: P x): ap pr1 (lift u p) = p.
Proof.
  induction p.
  apply idpath.
Defined.

Definition apd {A: UU} {P: ∏ x: A, UU} {x y: A} (f: ∏ x: A, P x) (p: x = y): p # (f x) = f y.
Proof.
  induction p.
  apply idpath.
Defined.

Definition transportconst {A B: UU} {x y: A} (f: A → B) (p: x = y) (b: B): p # b = b.
Proof.
  induction p.
  apply idpath.
Defined.

Lemma apf_transport {A B: UU} {x y: A} (f: A → B) (p: x = y): apd f p = transportconst f p (f x) ; ap f p.
Proof.
  induction p.
  apply idpath.
Defined.

Lemma transport_trans {A: UU} {P: ∏ x: A, UU} {x y z : A} (p: x = y) (q: y = z) (u: P x): q # (p # u) = (p ; q) # u.
Proof.
  induction p.
  apply idpath.
Defined.

Lemma transport_comp {A B: UU} (f: A → B) (P: ∏ x: B, UU) {x y: A} (p: x = y): 
  transport (P ∘ f) p = (transport P) (ap f p).
Proof.
  induction p.
  apply idpath.
Defined.

Lemma transport_comp2 {A B: UU} (f: A → B) (P: ∏ x: B, UU) {x y: A} (p: x = y): 
  transport (P ∘ f) p = (transport P) (ap f p).
Proof.
  induction p.
  apply idpath.
Defined.

Lemma transport_x {A: UU} {P Q: ∏ x: A, UU} (f: ∏ x: A, P x → Q x) {x y: A} (p: x = y) (u: P x):
  p # (f x u) = f y (p # u).
Proof.
  induction p.
  apply idpath.
Defined.

Definition homot {A: UU} {P: ∏ x: A, UU} (f g: sec P): UU := ∏ x: A, f x = g x.

Notation "f ~ g" := (homot f g).

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
  exact ((h1 x) ; (h2 x)).
Defined.

Lemma homot_comp_id_r {A B: UU} (f: A → B): f ∘ (idfun A) ~ f.
Proof.
  intro x.
  apply idpath.
Defined.

Lemma homot_comp_id_l {A B: UU} (f: A → B): (idfun B) ∘ f ~ f.
Proof.
  intro x.
  apply idpath.
Defined.

Lemma homot_assoc {A B C D: UU} (f: A → B) (g: B → C) (h: C → D): (h ∘ g) ∘ f ~ h ∘ (g ∘ f).
Proof.
 intro x.
 apply idpath.
Defined. 

Lemma homot_nat {A B : UU} (f g: A → B) (H: f ~ g) {x y : A} (p: x =  y): H x ; ap g p = ap f p ; H y.
Proof.
  induction p.
  cbn.
  rewrite paths_trans_rid.
  apply idpath.
Defined.

Corollary homot_nat_cor {A:  UU} (f: A → A) (H: f ~ idfun A) {x: A}: H (f x) = ap f (H x).
Proof.
  set (p := homot_nat f (idfun A) H (H x)).
  rewrite ap_idfun in p.
  unfold idfun in p.
  set (p' := right_whisker p (! (H x))).
  do 2 rewrite <- paths_trans_assoc in p'.
  rewrite paths_tran_refl1 in p'.
  do 2 rewrite paths_trans_rid in p'.
  exact p'.
Defined.

Definition qinv {A B: UU} (f: A → B) := ∑ g: B → A,  (f ∘ g ~ idfun B) × (g ∘ f ~ idfun A) .

Definition qinv_to_fun {A B: UU} {f: A → B} (qinvf: qinv f) := pr1 qinvf.

Definition qinv_proof_r {A B: UU} {f: A → B} (qinvf: qinv f) :=  pr1 (pr2 qinvf).

Definition qinv_proof_l {A B: UU} {f: A → B} (qinvf: qinv f) :=  pr2 (pr2 qinvf).

Coercion qinv_to_fun: qinv >-> Funclass.

Definition qinv_idfun {A: UU}: qinv (idfun A).
Proof.
  unfold qinv.
  exists (idfun A).
  split; apply homot_comp_id_l.
Defined.

Definition isequiv {A B: UU} (f: A → B) := (∑ g: B → A, f ∘ g ~ idfun B) × (∑ h: B → A, h ∘ f ~ idfun A).

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
  - set (γ1 := λ x: B, ap h (α x)).
    unfold funcomp, idfun in γ1.
    set (γ2 := λ x: B, β(g x)).
    unfold funcomp, idfun in γ2.
    set (γ := λ x: B, ! γ2 x ; γ1 x). 
    intro x.
    unfold funcomp, idfun.
    exact (γ (f x) ; β x).
Defined.

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
  split.
  - intro x.
    set (α := ap g (qinv_proof_r e1 (e2 x))).
    set (β := qinv_proof_r e2 x).
    exact (α ; β).
  - intro x.
    set (α := ap e1 (qinv_proof_l e2 (f x))).
    set (β := qinv_proof_l e1 x).
    exact (α ; β).
Defined.

Definition equiv (A B: UU) := ∑ f: A → B, isequiv f.

Lemma equiv_refl {A: UU}: equiv A A.
Proof.
  exists (idfun A).
  apply isequiv_idfun.
Defined.

Lemma isequiv_symm {A B: UU} (e: equiv A B): equiv B A.
Proof.
  induction e as [f finv].
  apply isequiv_to_qinv in finv.
  exists finv.
  apply qinv_to_isequiv.
  unfold isequiv.
  exists f.
  split.
  - apply (qinv_proof_l finv).
  - apply (qinv_proof_r finv).
Defined.

Definition pair_eq_inv {A B: UU} (x y: A × B): x = y →  (pr1 x = pr1 y) × (pr2 x = pr2 y) 
  :=  λ p, (ap prod_pr1 p) ,, (ap prod_pr2 p).

Definition pair_eq {A B: UU} (x y: A × B): (pr1 x = pr1 y) × (pr2 x = pr2 y) → x = y.
Proof.
  induction x as [a b].
  induction y as [c d].
  cbv.
  intro p.
  induction p as [p1 p2].
  induction p1.
  induction p2.
  apply idpath.
Defined.

Lemma pair_eq_qinv {A B: UU} {x y: A × B}: qinv (pair_eq_inv  x y).
Proof.
  exists (pair_eq x y).
  split.
  - intro p.
    induction x as [a b].
    induction y as [c d].
    cbv in p.
    induction p as [p1 p2].
    induction p1.
    induction p2.
    apply idpath.
  - intro p.
    induction p.
    apply idpath.
Defined.

Definition unit_path_inv (x y: unit): unit → ( x = y).
Proof.
  intro.
  induction x, y.
  apply idpath.
Defined.

Theorem unit_path (x y: unit): equiv (x = y) unit.
Proof.
  exists (λ _, tt).
  apply qinv_to_isequiv.
  exists (unit_path_inv x y).
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
  set (ax := funextAxiom f g).
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
  apply paths_refl1.
  apply funext_happly.
Defined.

Lemma funext_refl {A: UU} {P: A → UU} {f g: sec P} (α: f = g): ! α = funext (λ x, ! (happly α x)).
Proof.
  induction α.
  cbv - [funext].
  apply funext_idpath.  (* prende il posto di apply idapth perché usiamo un assioma *)
Defined.

Lemma funext_comp {A: UU} {P: A → UU} {f g h: sec P} (α: f = g) (β: g = h): α ; β  = funext (λ x, (happly α x) ; (happly β x)).
Proof.
  induction α.
  induction β.
  apply funext_idpath. (* prende il posto di apply idapth perché usiamo un assioma *)
Defined.

