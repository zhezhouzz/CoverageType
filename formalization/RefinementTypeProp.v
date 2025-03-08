From stdpp Require Import mapset.
From stdpp Require Import natmap.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import Qualifier.
From CT Require Import ListCtx.
From CT Require Import RefinementType.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import OperationalSemantics.
Import BasicTyping.
Import Qualifier.
Import ListCtx.
Import List.
Import RefinementType.

(** * Naming properties of refinement type syntax *)

(** * erase *)

Lemma rty_erase_open_eq τ : forall k s,
  rty_erase τ = rty_erase ({k ~r> s} τ).
Proof.
  induction τ; intros; simpl; eauto; f_equal; eauto.
Qed.

Lemma rty_erase_subst_eq ρ x s :
  rty_erase ρ = rty_erase ({x := s}r ρ).
Proof.
  induction ρ; simpl; eauto; f_equal; eauto.
Qed.

Lemma ctx_erase_lookup Γ x ρ :
  ctxfind Γ x = Some ρ ->
  ⌊Γ⌋* !! x = Some ⌊ρ⌋.
Proof.
  induction Γ; simpl; intros; try easy.
  destruct a. case_decide. simplify_eq.
  cbn. simplify_map_eq. reflexivity.
  simp_hyps.
  cbn. rewrite insert_empty. rewrite <- insert_union_singleton_l.
  simplify_map_eq. reflexivity.
Qed.

Lemma ctx_erase_app Γ Γ':
  ⌊Γ ++ Γ'⌋* = ⌊Γ⌋* ∪ ⌊Γ'⌋*.
Proof.
  induction Γ; simpl.
  - cbn. by rewrite map_empty_union.
  - destruct a. unfold ctx_erase in *. cbn. rewrite IHΓ.
    by rewrite map_union_assoc.
Qed.

Lemma ctx_erase_dom Γ :
  dom ⌊Γ⌋* ≡ ctxdom Γ.
Proof.
  induction Γ; simpl.
  - cbn. apply dom_empty.
  - destruct a. cbn in *.
    rewrite insert_empty.
    setoid_rewrite dom_union.
    rewrite dom_singleton.
    f_equiv. eauto.
Qed.

Lemma ctx_erase_app_r Γ x ρ :
  x # Γ ->
  ⌊Γ ++ [(x, ρ)]⌋* = <[x:=⌊ρ⌋]> ⌊Γ⌋*.
Proof.
  intros H.
  rewrite ctx_erase_app.
  cbn. rewrite map_union_empty. rewrite insert_empty.
  rewrite <- insert_union_singleton_r. auto.
  simpl in H. rewrite <- ctx_erase_dom in H.
  by apply not_elem_of_dom.
Qed.

(** * commute *)

Lemma subst_commute_rty : forall x u_x y u_y τ,
    x <> y -> x ∉ fv_value u_y -> y ∉ fv_value u_x ->
    {x := u_x }r ({y := u_y }r τ) = {y := u_y }r ({x := u_x }r τ).
Proof.
  induction τ; simpl; intros; f_equal;
    eauto using subst_commute_qualifier.
Qed.

Lemma subst_fresh_rty: forall (τ: rty) (x:atom) (u: value),
    x # τ -> {x := u}r τ = τ.
Proof.
  pose subst_fresh_qualifier.
  induction τ; simpl; intros; f_equal; eauto;
    solve [ auto_apply; my_set_solver
          | apply subst_fresh_am; my_set_solver ].
Qed.

Lemma open_fv_rty (τ : rty) (v : value) k :
  rty_fv ({k ~r> v} τ) ⊆ rty_fv τ ∪ fv_value v.
Proof.
  all: revert k.
  induction τ; simpl; intros; eauto using open_fv_qualifier.
  etrans. repeat apply union_mono; eauto.
  my_set_solver.
Qed.

Lemma open_fv_rty' (τ : rty) (v : value) k :
  rty_fv τ ⊆ rty_fv ({k ~r> v} τ).
Proof.
  pose open_fv_qualifier'.
  all: revert k.
  induction τ; simpl; intros; eauto using open_fv_qualifier';
    repeat apply union_mono; eauto.
Qed.

Lemma open_subst_same_rty: forall x y (τ : rty) k,
    x # τ ->
    {x := y }r ({k ~r> x} τ) = {k ~r> y} τ.
Proof.
  pose open_subst_same_qualifier.
  induction τ; simpl; intros; f_equal; eauto;
    auto_apply; my_set_solver.
Qed.

Lemma subst_open_rty: forall (τ: rty) (x:atom) (u: value) (w: value) (k: nat),
    lc w -> {x := w}r ({k ~r> u} τ) = ({k ~r> {x := w}v u} ({x := w}r τ)).
Proof.
  pose subst_open_qualifier.
  induction τ; simpl; intros; f_equal; eauto.
Qed.

Lemma subst_open_rty_closed:
  ∀ (ρ : rty) (x : atom) (u w : value) (k : nat),
    closed_value u ->
    lc w → {x := w }r ({k ~r> u} ρ) = {k ~r> u} ({x := w }r ρ).
Proof.
  intros. rewrite subst_open_rty; auto.
  rewrite (subst_fresh_value); eauto. set_solver.
Qed.

Lemma subst_open_var_rty: forall x y (u: value) (τ: rty) (k: nat),
    x <> y -> lc u -> {x := u}r ({k ~r> y} τ) = ({k ~r> y} ({x := u}r τ)).
Proof.
  intros.
  rewrite subst_open_rty; auto. simpl. rewrite decide_False; auto.
Qed.

Ltac solve_fine_rty :=
  repeat fine_rty_simp_aux; eauto;
  match goal with
  | [ _ : _ |- context [rty_subst _ _ ?ρ] ] =>
      destruct ρ; simpl in *; eauto; intuition
  | [ _ : _ |- fine_rty _ ] =>
      simpl in *;
      intuition; eauto
  end.

Lemma subst_lc_rty : forall x (u: value) (τ: rty),
    lc_rty τ -> lc u -> lc_rty ({x := u}r τ).
Proof.
  pose subst_lc_phi1.
  all: induction 1; intros; simpl in *.
  - econstructor; simpl; eauto.
  - auto_exists_L.
  - auto_exists_L; intros. rewrite <- subst_open_var_rty; eauto.
    auto_apply; eauto. my_set_solver. my_set_solver.
    simpl. intuition. fine_rty_simp_aux. fine_rty_solver.
Qed.

Lemma fv_of_subst_rty_closed:
  forall x (u : value) (τ: rty),
    closed_value u ->
    rty_fv ({x := u }r τ) = (rty_fv τ ∖ {[x]}).
Proof.
  induction τ; simpl; intros; eauto using fv_of_subst_qualifier_closed;
  try (rewrite !fv_of_subst_td_closed by eauto); my_set_solver.
Qed.

Lemma open_not_in_eq_rty (x : atom) (τ : rty) k :
  x # {k ~r> x} τ ->
  forall e, τ = {k ~r> e} τ.
Proof.
  pose open_not_in_eq_qualifier.
  generalize k; induction τ; intros; simpl in *; f_equal; eauto;
    try (auto_apply; my_set_solver).
Qed.

Lemma subst_intro_rty: forall (ρ: rty) (x:atom) (w: value) (k: nat),
    x # ρ ->
    lc w -> {x := w}r ({k ~r> x} ρ) = ({k ~r> w} ρ).
Proof.
  intros.
  specialize (subst_open_rty ρ x x w k) as J.
  simpl in J. rewrite decide_True in J; auto.
  rewrite J; auto. rewrite subst_fresh_rty; auto.
Qed.


Lemma lc_subst_rty: forall x (u: value) (τ: rty), lc_rty ({x := u}r τ) -> lc u -> lc_rty τ.
Proof.
  pose lc_subst_phi1.
  pose lc_subst_phi2.
  pose lc_rty_fine.
  intros.
  remember (({x:=u}r) τ).
  generalize dependent τ.
  induction H.
  - intros τ **; destruct τ; inversion Heqr; simpl in *; subst; econstructor; eauto.
  - intros τ1 **; destruct τ1; inversion Heqr; simpl; subst.
    auto_exists_L.
  - intros τ1 **; destruct τ1; inversion Heqr; simpl; subst.
    auto_exists_L.
    intros. repeat specialize_with x0.
    apply H1.
    rewrite <- subst_open_var_rty; eauto. my_set_solver. fine_rty_solver.
Qed.

Lemma open_rty_idemp: forall u (v: value)  (τ: rty) (k: nat),
    lc v ->
    {k ~r> u} ({k ~r> v} τ) = {k ~r> v} τ.
Proof.
  pose open_qualifier_idemp.
  induction τ; intros; simpl; f_equal; eauto.
Qed.

Lemma closed_rty_subseteq_proper s1 s2 ρ :
  closed_rty s1 ρ ->
  s1 ⊆ s2 ->
  closed_rty s2 ρ.
Proof.
  intros. sinvert H. split. eauto.
  my_set_solver.
Qed.

Lemma fact1_rty: forall (u v: value) (A: rty) i j,
    i <> j -> {i ~r> u} ({j ~r> v} A) = {j ~r> v} A -> {i ~r> u} A = A.
Proof.
  pose fact1_value.
  pose fact1_qualifier.
  intros u v. induction A; simpl; intros; eauto; f_equal; simp_hyps; eauto.
Qed.

Lemma open_rec_lc_rty: ∀ (u : value) τ (k : nat), lc_rty τ -> {k ~r> u} τ = τ.
Proof.
  pose open_rec_lc_phi1.
  intros. generalize dependent k.
  induction H; simpl; intros; auto; f_equal; eauto;
    try (rewrite open_rec_lc_value; eauto).
  - auto_pose_fv x. apply fact1_rty with (j := 0) (v := x); eauto.
    rewrite H0; eauto. my_set_solver.
Qed.

Lemma body_rty_open_lc: forall (v: value) τ,
    lc v -> (body_rty τ) -> lc_rty (τ ^r^ v).
Proof.
  unfold body_rty. intros. simp_hyps.
  auto_pose_fv x.
  erewrite <- open_subst_same_rty. instantiate (1:= x).
  apply subst_lc_rty; eauto.
  apply H0.
  all: my_set_solver.
Qed.

Lemma flip_rty_open τ k v: {k ~r> v} (flip_rty τ) = flip_rty ({k ~r> v} τ).
Proof.
  destruct τ; simpl; intros; intuition.
Qed.

Lemma flip_rty_subst τ x v: {x:=v}r (flip_rty τ) = flip_rty ({x:=v}r τ).
Proof.
  destruct τ; simpl; intros; intuition.
Qed.
