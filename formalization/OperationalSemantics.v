From stdpp Require Import mapset.
From CT Require Import CoreLang.
From CT Require Import CoreLangProp.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.

Inductive eval_op: effop -> constant -> constant -> Prop :=
| eval_op_plus_one: forall (a: nat), eval_op op_plus_one a (1 + a)
| eval_op_eq_zero: forall (a: nat), eval_op op_eq_zero a (Nat.eqb a 0)
| eval_op_rannat: forall (a b: nat), eval_op op_rannat a b.

Global Hint Constructors eval_op: core.

Notation "'⇓{' op '~' c1 '}{' c '}' " := (eval_op op c1 c)
                                           (at level 30, format "⇓{ op ~ c1 }{ c }", c1 constr, c constr).

(** This file defines the operational semantics of the core language. *)

Reserved Notation "t1 '↪' t2" (at level 60, t1 constr, t2 constr).

Inductive step : tm -> tm -> Prop :=
| STEffOp: forall op (c1 c: constant) e,
    body e -> lc c1 -> lc c ->
    ⇓{op ~ c1}{c} -> (tleteffop op c1 e) ↪ (e ^t^ c)
| STLetE1: forall e1 e1' e,
    body e ->
    e1 ↪ e1' ->
    (tlete e1 e) ↪ (tlete e1' e)
| STLetE2: forall (v1: value) e,
    lc v1 -> body e ->
    (tlete (treturn v1) e) ↪ (e ^t^ v1)
| STLetAppLam: forall T (v_x: value) e1 e,
    body e1 -> body e -> lc v_x ->
    (tletapp (vlam T e1) v_x e) ↪ tlete (e1 ^t^ v_x) e
| STLetAppFix: forall T_f (v_x: value) (e1: tm) e,
    body (vlam T_f e1) -> lc v_x -> body e ->
    tletapp (vfix T_f (vlam T_f e1)) v_x e ↪
      tletapp ((vlam T_f e1) ^v^ v_x) (vfix T_f (vlam T_f e1)) e
| STMatchbTrue: forall e1 e2,
    lc e1 -> lc e2 ->
    (tmatchb true e1 e2) ↪ e1
| STMatchbFalse: forall e1 e2,
    lc e1 -> lc e2 ->
    (tmatchb false e1 e2) ↪ e2
where "t1 '↪' t2" := (step t1 t2).

Inductive multistep : tm -> tm -> Prop :=
| multistep_refl : forall (e : tm),
    lc e -> multistep e e
| multistep_step : forall (x y z: tm),
    x ↪ y ->
    multistep y z ->
    multistep x z.

Notation " t1 '↪*' t2" := (multistep t1 t2) (at level 60, t1 constr, t2 constr).

Global Hint Constructors multistep : core.

(** * Properties of operational semantics *)

Lemma step_regular: forall e1 e2, e1 ↪ e2 -> lc e1 /\ lc e2.
Proof.
  intros.
  induction H; split; auto.
  - destruct H. econstructor; auto. apply H.
  - apply open_lc_tm; auto.
  - destruct_hyp_conj. rewrite lete_lc_body; split; auto.
  - destruct_hyp_conj. rewrite lete_lc_body; split; auto.
  - try destruct_hyp_conj. rewrite lete_lc_body; split; auto.
  - apply open_lc_tm; auto.
  - rewrite letapp_lc_body; split; auto. rewrite lc_abs_iff_body; auto.
  - rewrite lete_lc_body; split; auto. apply open_lc_tm; auto.
  - rewrite letapp_lc_body; split; auto. rewrite lc_fix_iff_body; auto.
  - rewrite letapp_lc_body; split; auto.
    + eapply open_lc_value; eauto.
    + rewrite body_vlam_eq in H. rewrite lc_fix_iff_body; eauto.
Qed.

Lemma step_regular1: forall e1 e2, e1 ↪ e2 -> lc e1.
Proof.
  intros. apply step_regular in H. destruct H; auto.
Qed.

Lemma step_regular2: forall e1 e2, e1 ↪ e2 -> lc e2.
Proof.
  intros. apply step_regular in H. destruct H; auto.
Qed.

Global Hint Resolve step_regular1: core.
Global Hint Resolve step_regular2: core.

Theorem multistep_trans: forall (x y z : tm), x ↪* y -> y ↪* z -> x ↪* z.
Proof.
  intros. generalize dependent z.
  induction H; intros; eauto.
Qed.

Theorem multistep_R : forall (x y : tm),
    x ↪ y -> x ↪* y.
Proof. intros. eauto.
Qed.

Lemma multi_step_regular: forall e1 e2, e1 ↪* e2 -> lc e1 /\ lc e2.
Proof.
  induction 1; intuition eauto.
Qed.

Lemma multi_step_regular1: forall e1 e2, e1 ↪* e2 -> lc e1.
Proof.
  intros. apply multi_step_regular in H. destruct H; auto.
Qed.

Lemma multi_step_regular2: forall e1 e2, e1 ↪* e2 ->  lc e2.
Proof.
  intros. apply multi_step_regular in H. destruct H; auto.
Qed.

Ltac step_regular_simp :=
  repeat match goal with
    | [H: _ ↪* _ |- lc _ ] => apply multi_step_regular in H; destruct H; auto
    | [H: _ ↪ _ |- lc _ ] => apply step_regular in H; destruct H; auto
    | [H: _ ↪* _ |- body _] => apply multi_step_regular in H; destruct H; auto
    | [H: _ ↪ _ |- body _] => apply step_regular in H; destruct H; auto
    end.

Lemma value_reduction_refl: forall (v1: value) v2, v1 ↪* v2 -> v2 = v1.
Proof.
  intros * H. sinvert H; easy.
Qed.

Ltac reduction_simp :=
  match goal with
  | H: (treturn _) ↪* _  |- _ =>
      apply value_reduction_refl in H; simp_hyps; simplify_eq
  end.

Lemma reduction_tlete:  forall e_x e (v : value),
    tlete e_x e ↪* v -> (exists (v_x: value), e_x ↪* v_x /\ (e ^t^ v_x) ↪* v).
Proof.
  intros.
  remember (tlete e_x e). remember (treturn v).
  generalize dependent e_x.
  induction H; intros; subst. easy.
  sinvert H.
  - ospecialize* IHmultistep; eauto.
    simp_hyps. repeat esplit; eauto.
  - repeat esplit. econstructor; eauto. eauto.
Qed.

Lemma reduction_tlete':  forall e_x e (v_x v : value),
    (* NOTE: This condition is unnecessary as it should be implied by the
    regularity lemma. Remove later when we bother proving a few more naming
    lemmas. *)
    body e ->
    e_x ↪* v_x ->
    (e ^t^ v_x) ↪* v ->
    tlete e_x e ↪* v.
Proof.
  intros * Hb H. remember (treturn v_x).
  induction H; intros; subst.
  - econstructor; eauto using STLetE2.
  - simp_hyps.
    simplify_list_eq.
    econstructor.
    econstructor; eauto.
    eauto.
Qed.

Lemma reduction_tlete_iff:
  ∀ (e_x e : tm) (v : value),
    tlete e_x e ↪* v
    <-> (body e /\ ∃ (v_x : value),
          e_x ↪* v_x ∧ e ^t^ v_x ↪* v).
Proof.
  split.
  - split. apply multi_step_regular in H. simp_hyps. lc_solver.
    apply reduction_tlete; eauto.
  - intros. simp_hyps. eapply reduction_tlete'; eauto.
Qed.

Lemma reduction_mk_app_v_v (f v_x v : value) :
  lc v_x ->
  mk_app f v_x ↪* v ->
  tletapp f v_x (vbvar 0) ↪* v.
Proof.
  intros Hlc H.
  sinvert H. sinvert H0. easy.
  sinvert H1. sinvert H. easy.
  simpl in *. simplify_list_eq.
  repeat rewrite open_rec_lc_value in * by eauto.
  eauto.
Qed.

Lemma body_mk_app_aux2 (f: value): lc f -> body (tletapp f (vbvar 0) (vbvar 0)).
Proof.
  eexists. instantiate_atom_listctx.
  simpl. apply letapp_lc_body. repeat split; eauto using lc.
  by rewrite open_rec_lc_value.
Qed.

Lemma body_mk_app_aux v_x:
  lc v_x ->
  body (tlete v_x (tletapp (vbvar 1) (vbvar 0) (vbvar 0))).
Proof.
  eexists. instantiate_atom_listctx.
  simpl. apply lete_lc_body. repeat split; eauto using lc.
  by rewrite open_rec_lc_tm.
Qed.

Lemma reduction_mk_app_v_v' (f v_x v : value) :
  tletapp f v_x (vbvar 0) ↪* v ->
  mk_app f v_x ↪* v.
Proof.
  intros H.
  assert (lc v_x). {
    apply multi_step_regular1 in H. sinvert H. eauto.
  }
  assert (lc f). {
    apply multi_step_regular1 in H. sinvert H. eauto.
  }
  eapply_eq multistep_step.
  eapply STLetE2.
  - apply multi_step_regular1 in H. sinvert H. eauto.
  (* Probably should be a lemma. *)
  - apply body_mk_app_aux; eauto.
  - simpl. simplify_list_eq. rewrite open_rec_lc_value; eauto.
    eapply_eq multistep_step.
    eapply STLetE2; eauto.
    simpl. by rewrite open_rec_lc_value.
Qed.

Lemma open_vlam_rev k Tb e (v: value): vlam Tb ({S k ~t> v} e) = {k ~v> v} vlam Tb e.
Proof. eauto. Qed.

Lemma reduction_mk_app_lam Tb e (v_x : value) (v : value) :
  lc v_x ->
  mk_app (vlam Tb e) v_x ↪* v ->
  e ^t^ v_x ↪* v.
Proof.
  unfold mk_app. intros Hlc H.
  assert (lc (vlam Tb e)) as Haux. {
    step_regular_simp. sinvert H; eauto.
  }
  apply reduction_tlete in H. simp_hyps. simpl in *.
  rewrite open_rec_lc_value in H1; eauto.
  apply value_reduction_refl in H0; sinvert H0.
  apply reduction_tlete in H1. simp_hyps. simpl in *.
  rewrite open_vlam_rev in H1.
  rewrite open_rec_lc_value in H1; eauto.
  apply value_reduction_refl in H0; sinvert H0.
  sinvert H1. sinvert H.
  apply reduction_tlete in H0.
  simp_hyps. simpl in *.
  eapply multistep_trans; eauto.
Qed.

Lemma reduction_mk_app_lam' Tb e (v_x : value) (v : value) :
  lc v_x ->
  (* NOTE: This condition is unnecessary as it should be implied by the
  regularity lemma. *)
  body e ->
  e ^t^ v_x ↪* v ->
  mk_app (vlam Tb e) v_x ↪* v.
Proof.
  unfold mk_app. intros Hlc Hb H.
  assert (lc (vlam Tb e)) as Haux by lc_solver.
  apply reduction_tlete' with (v_x := vlam Tb e); eauto.
  apply body_mk_app_aux; eauto.
  simpl. rewrite open_rec_lc_value; eauto.
  apply reduction_tlete' with (v_x := v_x); eauto.
  simpl. rewrite open_vlam_rev; rewrite open_rec_lc_value; eauto.
  eapply_eq multistep_step. econstructor; eauto.
  apply reduction_tlete' with (v_x := v); eauto.
  simpl. econstructor. eauto using multi_step_regular2.
Qed.

Ltac value_reduction_simp :=
  repeat
    match goal with
    | [H: treturn _ ↪* treturn _ |- _ ] => apply value_reduction_refl in H; sinvert H
    end.

Lemma reduction_tletapp:  forall v1 v2 e (v : value),
    tletapp v1 v2 e ↪* v ->
    (exists (v_x: value), tletapp v1 v2 (vbvar 0) ↪* v_x /\ (e ^t^ v_x) ↪* v).
Proof.
  intros.
  remember (tletapp v1 v2 e). remember (treturn v).
  generalize dependent v2.
  generalize dependent v1.
  induction H; intros; subst. easy.
  simp_hyps. sinvert H.
  - eapply reduction_tlete in H0. simp_hyps.
    simplify_list_eq.
    eexists _. repeat split; eauto using reduction_mk_app_lam'.
    eapply_eq multistep_step. econstructor; eauto.
    eapply reduction_tlete'; eauto. simpl.
    econstructor. apply multi_step_regular2 in H0; eauto.
  - simplify_list_eq.
    ospecialize* H1; eauto. simp_hyps.
    eexists _.
    repeat split; cycle 1; eauto.
    eapply_eq multistep_step. econstructor; eauto.
    simpl. eauto.
Qed.

Lemma reduction_tletapp':  forall v1 v2 e (v : value),
    (body e /\ exists (v_x: value), tletapp v1 v2 (vbvar 0) ↪* v_x /\ (e ^t^ v_x) ↪* v) -> tletapp v1 v2 e ↪* v.
Proof.
  intros. destruct H as (He & (v_x & Hv_x & H)).
  remember (tletapp v1 v2 (vbvar 0)). remember (treturn v_x).
  generalize dependent v2.
  generalize dependent v1.
  generalize dependent v_x.
  induction Hv_x; intros; subst. easy.
  simp_hyps. sinvert H.
  - clear IHHv_x.
    eapply reduction_tlete in Hv_x. simp_hyps.
    simplify_list_eq. value_reduction_simp.
    eapply_eq multistep_step. econstructor; eauto.
    eapply reduction_tlete'; eauto.
  - simplify_list_eq.
    ospecialize* IHHv_x; eauto.
    eapply_eq multistep_step. econstructor; eauto.
    simpl. eauto.
Qed.

Lemma reduction_tletapp_iff:  forall v1 v2 e (v : value),
    tletapp v1 v2 e ↪* v <-> (body e /\ exists (v_x: value), tletapp v1 v2 (vbvar 0) ↪* v_x /\ (e ^t^ v_x) ↪* v).
Proof.
  split; intros.
  - split. apply multi_step_regular1 in H. lc_solver.
    apply reduction_tletapp; eauto.
  - apply reduction_tletapp'; eauto.
Qed.

Lemma value_reduction_any_ctx: forall (v1: value), lc v1 -> v1 ↪* v1.
Proof.
  intros. econstructor; eauto.
Qed.

Lemma reduction_tleteffop:  forall op v2 e (v : value),
    (tleteffop op v2 e) ↪* v ->
    exists (c2 c_x: constant),
      v2 = c2 /\ ⇓{op ~ c2}{ c_x } /\ (e ^t^ c_x) ↪* v.
Proof.
  intros.
  sinvert H. sinvert H0.
  eauto 10.
Qed.


Lemma reduction_tleteffop_iff:  forall op v2 e (v : value),
    (tleteffop op v2 e) ↪* v <->
      body e /\ exists (c2 c_x: constant),
        v2 = c2 /\ ⇓{op ~ c2}{ c_x } /\ (e ^t^ c_x) ↪* v.
Proof.
  split.
  - intuition.
    + apply multi_step_regular in H. simp_hyps. rewrite leteffop_lc_body in H. intuition.
    + apply reduction_tleteffop; eauto.
  - intros. simp_hyps. subst. repeat (econstructor; eauto).
Qed.

Lemma reduction_matchb_true:  forall e1 e2 (v : value),
    tmatchb true e1 e2 ↪* v -> e1 ↪* v.
Proof.
  intros.
  sinvert H.
  sinvert H0. simplify_list_eq. eauto.
Qed.

Lemma reduction_matchb_false:  forall e1 e2 (v : value),
    tmatchb false e1 e2 ↪* v -> e2 ↪* v.
Proof.
  intros.
  sinvert H.
  sinvert H0. simplify_list_eq. eauto.
Qed.

(** NOTE: reduction lemmas for underapproximation *)

Ltac lc_solver_simp_aux :=
  match goal with
  | [H: _ ↪* _ |- lc _] => apply multi_step_regular in H; simp_hyps
  | [H: _ ↪* _ |- body _] => apply multi_step_regular in H; simp_hyps
  end.

Ltac lc_solver_simp :=
  repeat lc_solver_simp_aux; eauto.

Ltac lc_solver_plus_aux :=
  match goal with
  | [H: lc (tlete _ _) |- lc _] => rewrite lete_lc_body in H; simp_hyps
  | [H: lc (tlete _ _) |- body _] => rewrite lete_lc_body in H; simp_hyps
  end.

Ltac lc_solver_plus :=
  eauto; lc_solver_simp; eauto;
  (repeat lc_solver_plus_aux); eauto.

Lemma reduction_tlete_value: forall (v1: value) e2,
  forall (v: value), tlete v1 e2 ↪* v <-> (lc v1 /\ body e2 /\ e2 ^t^ v1 ↪* v).
Proof.
  split; intros.
  - assert (lc v1) by lc_solver_plus.
    assert (body e2) by lc_solver_plus. intuition.
    apply reduction_tlete in H. simp_hyps.
    apply value_reduction_refl in H2. simp_hyps. subst; intuition.
  - simp_hyps. eapply reduction_tlete'; eauto.
Qed.

Lemma reduction_nest_tlete: forall e,
  forall (v: value), tlete e (vbvar 0) ↪* v <-> e ↪* v.
Proof.
  intros e. split; intros.
  - apply reduction_tlete in H. simp_hyps. simpl in *.
    apply value_reduction_refl in H1.
    simp_hyps. subst. eauto.
  - eapply reduction_tlete'; eauto. simpl.
    apply (value_reduction_any_ctx v); eauto.
    apply multi_step_regular2 in H; eauto.
Qed.

Lemma reduction_tletapp_lam:  forall T e1 v2 e (v : value),
    tletapp (vlam T e1) v2 e ↪* v <->
      (lc v2 /\ lc (vlam T e1) /\ tlete (e1 ^t^ v2) e ↪* v).
Proof.
  split; intros.
  - inversion H; subst. inversion H0; subst; eauto.
    intuition; eauto. lc_solver.
  - simp_hyps. eapply_eq multistep_step; eauto.
    apply multi_step_regular1 in H2; eauto.
    rewrite lete_lc_body in H2; simp_hyps; eauto.
    econstructor; eauto. lc_solver.
Qed.

Lemma reduction_tletapp_fix:  forall T_f (v_x: value) (e1: tm) e (v : value),
      tletapp (vfix T_f (vlam T_f e1)) v_x e ↪* v <->
        (lc v_x /\ tletapp ((vlam T_f e1) ^v^ v_x) (vfix T_f (vlam T_f e1)) e ↪* v).
Proof.
  split; intros.
  - inversion H; subst. inversion H0; subst; eauto.
    (* intuition; eauto. lc_solver. *)
  - simp_hyps. eapply_eq multistep_step; eauto.
    apply multi_step_regular in H0; simp_hyps; eauto.
    econstructor; eauto. rewrite letapp_lc_body in H0. simp_hyps.
    lc_solver. lc_solver.
Qed.

Lemma reduction_mk_app_iff:  forall e e_x (v : value),
    lc e_x ->
    mk_app e e_x ↪* v <->
      (exists (f v_x: value), e ↪* f /\ e_x ↪* v_x /\ tletapp f v_x (vbvar 0) ↪* v).
Proof.
  intros e e_x v Hlc.
  unfold mk_app.
  split; intros.
  - apply reduction_tlete in H. destruct H as (f & Hf & H).
    simpl in H. rewrite open_rec_lc_tm in H by eauto.
    apply reduction_tlete in H. destruct H as (v_x & Hv_x & H).
    simpl in H. rewrite open_rec_lc_value in H by lc_solver_plus.
    exists f, v_x. intuition.
  - destruct H as (f & v_x & Hf & Hv_x & H).
    eapply reduction_tlete'; eauto. apply body_mk_app_aux; eauto.
    simpl. rewrite open_rec_lc_tm; eauto.
    eapply reduction_tlete'; eauto. apply body_mk_app_aux2. by lc_solver_plus.
    simpl. rewrite open_rec_lc_value; eauto.
    all: by lc_solver_plus.
Qed.
