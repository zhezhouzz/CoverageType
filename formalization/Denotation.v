From stdpp Require Import mapset.
From stdpp Require Import natmap.
From Coq.Program Require Import Wf.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import RefinementTypeProp.
From CT Require Import Instantiation.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import ListCtx.
Import OperationalSemantics.
Import BasicTyping.
Import Qualifier.
Import RefinementType.

(** This file defines type denotations in λᴱ (Fig. 7). *)

(** Type Denotation *)

(** Refinement type and Hoare automata type denotation (Fig. 7) *)
(* The first argument is an overapproximation of the "size" of [ρ] or [τ]. In
other words, it is the "fuel" to get around Coq's termination checker. As long
as it is no less than [rty_measure] and [rty_measure], the denotation will not
hit bottom. Note that this is _different_ from the step used in step-indexed
logical relation. *)

(* Definition pure_tm (e: tm) := forall e' α β, α ⊧ e ↪*{β} e' -> α = β. *)

Fixpoint rtyR (gas: nat) (ρ: rty) (e: tm) : Prop :=
  match gas with
  | 0 => False
  | S gas' =>
      ∅ ⊢t e ⋮t ⌊ ρ ⌋ /\ closed_rty ∅ ρ /\
        match ρ with
        | {: b | ϕ} => exists (v: value), e = v /\ ⟦ ϕ ^q^ v ⟧q
        | [: b | ϕ] => forall (v: value), ⟦ ϕ ^q^ v ⟧q -> e ↪* v
        | ρx ⇨ τ =>
            exists (v: value),
            e ↪* v /\
              match ρx with
              | [: _ | _ ] =>
                  forall (e_x: tm), rtyR gas' ρx e_x -> rtyR gas' τ (mk_app v e_x)
              | _ =>
                  forall (v_x: value), rtyR gas' ρx v_x -> rtyR gas' (τ ^r^ v_x) (mk_app v v_x)
              end
        end
  end.

Notation "'⟦' τ '⟧' " := (rtyR (rty_measure τ) τ) (at level 20, format "⟦ τ ⟧", τ constr).

(** Context denotation (Fig. 7), defined as an inductive relation instead of a
  [Prop]-valued function. *)
Inductive ctxRst: listctx rty -> pp -> Prop :=
| ctxRst0: ctxRst [] (fun env => env = ∅)
| ctxRst1: forall Γ pp (x: atom) b ϕ,
    ctxRst Γ pp ->
    (* [ok_ctx] implies [ρ] is closed and valid, meaning that it does not use
    any function variables. *)
    ok_ctx (Γ ++ [(x, {: b | ϕ})]) ->
    ctxRst (Γ ++ [(x, {: b | ϕ})])
      (fun env => exists env', pp env' /\ forall (v: value), ⟦ m{ env }r {: b | ϕ} ⟧ v -> env' = <[ x := v ]> env)
| ctxRst2: forall Γ pp (x: atom) b ϕ,
    ctxRst Γ pp ->
    (* [ok_ctx] implies [ρ] is closed and valid, meaning that it does not use
    any function variables. *)
    ok_ctx (Γ ++ [(x, [: b | ϕ])]) ->
    ctxRst (Γ ++ [(x, [: b | ϕ])])
      (fun env => exists env', pp env' /\ exists (v: value), ⟦ m{ env }r {: b | ϕ} ⟧ v /\ env' = <[ x := v ]> env)
.


(** * Properties of denotation *)

Lemma langA_closed n a α β:
  langA n a α β -> closed_td ∅ a.
Proof.
  destruct n; simpl; intuition.
Qed.

Lemma langA_valid_trace n a α β:
  langA n a α β -> valid_trace α /\ valid_trace β.
Proof.
  destruct n; simpl; intuition.
Qed.

Lemma rtyR_typed_closed gas τ e :
  rtyR gas τ e ->
  ∅ ⊢t e ⋮t ⌊ τ ⌋ /\ closed_rty ∅ τ.
Proof.
  destruct gas; simpl; tauto.
Qed.

Lemma rtyR_closed_tm gas ρ e :
  rtyR gas ρ e ->
  closed_tm e.
Proof.
  intros H.
  apply rtyR_typed_closed in H.
  destruct H as (H&_).
  apply basic_typing_contains_fv_tm in H.
  my_set_solver.
Qed.

Lemma rtyR_closed_value gas ρ (v : value) :
  rtyR gas ρ v ->
  closed_value v.
Proof.
  intros H.
  apply rtyR_closed_tm in H.
  eauto.
Qed.

Lemma rtyR_lc gas ρ e :
  rtyR gas ρ e ->
  lc e.
Proof.
  intros H.
  apply rtyR_typed_closed in H.
  destruct H as (H&_).
  eauto using basic_typing_regular_tm.
Qed.

Lemma ctxRst_closed_env Γ Γv : ctxRst Γ Γv -> closed_env Γv.
Proof.
  unfold closed_env.
  induction 1.
  - apply map_Forall_empty.
  - apply map_Forall_insert_2; eauto.
    unfold closed_value.
    change (fv_value v) with (fv_tm v).
    apply equiv_empty.
    erewrite <- dom_empty.
    eapply basic_typing_contains_fv_tm.
    eapply rtyR_typed_closed.
    eauto.
Qed.

Lemma ctxRst_lc Γ Γv :
  ctxRst Γ Γv ->
  map_Forall (fun _ v => lc (treturn v)) Γv.
Proof.
  induction 1.
  apply map_Forall_empty.
  apply map_Forall_insert_2; eauto.
  apply rtyR_typed_closed in H1. simp_hyps.
  eauto using basic_typing_regular_tm.
Qed.

Lemma ctxRst_dom Γ Γv :
  ctxRst Γ Γv ->
  ctxdom Γ ≡ dom Γv.
Proof.
  induction 1; simpl; eauto.
  rewrite ctxdom_app_union.
  rewrite dom_insert.
  simpl. my_set_solver.
Qed.

Lemma ctxRst_ok_ctx Γ Γv :
  ctxRst Γ Γv ->
  ok_ctx Γ.
Proof.
  induction 1; eauto. econstructor.
Qed.

Lemma ctxRst_regular Γ Γv:
  ctxRst Γ Γv -> ok_ctx Γ /\ ctxdom Γ ≡ dom Γv /\ closed_env Γv.
Proof.
  pose ctxRst_ok_ctx. pose ctxRst_dom. pose ctxRst_closed_env. intuition; eauto.
Qed.

Lemma ctxRst_ok_insert Γ Γv x ρ :
  ctxRst Γ Γv ->
  ok_ctx (Γ ++ [(x, ρ)]) ->
  Γv !! x = None.
Proof.
  inversion 2; listctx_set_simpl.
  rewrite ctxRst_dom in * by eauto.
  by apply not_elem_of_dom.
Qed.


Lemma mk_top_closed_rty b : closed_rty ∅ (mk_top b).
Proof.
  econstructor. unshelve (repeat econstructor). exact ∅.
  my_set_solver.
Qed.

(* Lemma mk_top_denote_rty (b : base_ty) (v : value) : *)
(*   ∅ ⊢t v ⋮v b -> *)
(*   ⟦ mk_top b ⟧ v. *)
(* Proof. *)
(*   intros. *)
(*   split; [| split]; simpl; eauto using mk_top_closed_rty. *)
(* Qed. *)

Lemma mk_eq_constant_closed_rty c : closed_rty ∅ (mk_eq_constant c).
Proof.
  econstructor. unshelve (repeat econstructor). exact ∅.
  my_set_solver.
Qed.

Lemma mk_eq_constant_over_closed_rty c : closed_rty ∅ (mk_eq_constant_over c).
Proof.
  econstructor. unshelve (repeat econstructor). exact ∅.
  my_set_solver.
Qed.

Lemma mk_eq_constant_denote_rty c:
  ⟦ mk_eq_constant c ⟧ c.
Proof.
  simpl. split; [| split]; cbn; eauto using mk_eq_constant_closed_rty.
  intros.
  pose value_reduction_any_ctx.
  destruct v; simpl in *; try hauto.
Qed.

Lemma mk_eq_constant_over_denote_rty c:
  ⟦ mk_eq_constant_over c ⟧ c.
Proof.
  simpl. split; [| split]; cbn; eauto using mk_eq_constant_over_closed_rty.
  intros.
  apply value_reduction_refl' in H.
  destruct v; simpl in *; try hauto.
Qed.

Lemma closed_base_rty_qualifier_and B ϕ1 ϕ2 Γ:
  closed_rty Γ {: B | ϕ1 } ->
  closed_rty Γ {: B | ϕ2 } ->
  closed_rty Γ {: B | ϕ1 & ϕ2}.
Proof.
  pose lc_phi1_and.
  pose lc_phi2_and.
  intros [Hlc1 Hfv1] [Hlc2 Hfv2]. sinvert Hlc1. sinvert Hlc2.
  econstructor; eauto.
  econstructor; eauto.
  simpl in *.
  rewrite qualifier_and_fv. my_set_solver.
Qed.

Lemma denote_base_rty_qualifier_and B ϕ1 ϕ2 ρ:
  ⟦ {: B | ϕ1 } ⟧ ρ ->
  ⟦ {: B | ϕ2 } ⟧ ρ ->
  ⟦ {: B | ϕ1 & ϕ2} ⟧ ρ.
Proof.
  intros (?&?&?) (?&?&?).
  split; [| split]; eauto using closed_base_rty_qualifier_and.
  simp_hyps; subst. intros.
  rewrite qualifier_and_open.
  rewrite denote_qualifier_and.
  qauto.
Qed.

Ltac lia_simp :=
  repeat match goal with
    | [H: S _ = S _ |- _ ] => sinvert H
    end.

Ltac lia_tac :=
  repeat match goal with
  | [H: _ |- context [td_measure (_ ^a^ _)] ] => rewrite <- open_preserves_td_measure
  | [H: _ |- context [rty_measure (_ ^r^ _)] ] => rewrite <- open_preserves_rty_measure
  | [H: _ |- _ <= _ ] => simpl in *; lia
  end; eauto.

Ltac exist_tac :=
  match goal with
  | [H: exists x, _ |- exists _, _ ] =>
      let x := fresh x in
      destruct H as (x & H); exists x; intuition
  end.

Lemma langA_measure_irrelevant_aux: forall k ρ m n α β,
    td_measure ρ <= k ->
    k <= n ->
    k <= m ->
    langA n ρ α β <-> langA m ρ α β.
Proof.
  induction k; destruct ρ; intros m n α β Hk Hn Hm;
    split; intro H; destruct m, n;
    try solve [sinvert Hm; sinvert Hn; sinvert Hk; eauto];
    try solve [lia_tac];
    destruct H as (Hclosed & Hwfα & Hwfβ & H); simpl; intuition;
    try solve [exist_tac; rewrite IHk; try lia_tac].
  - left. rewrite IHk; try lia_tac.
  - right. rewrite IHk; try lia_tac.
  - left. rewrite IHk; try lia_tac.
  - right. rewrite IHk; try lia_tac.
  - rewrite IHk; try lia_tac.
  - rewrite IHk; try lia_tac.
Qed.

Lemma langA_measure_irrelevant: forall ρ m n α β,
    td_measure ρ <= n ->
    td_measure ρ <= m ->
    langA n ρ α β <-> langA m ρ α β.
Proof.
  intros. eapply (langA_measure_irrelevant_aux (td_measure ρ)); eauto.
Qed.

Lemma langA_measure_irrelevant' n ρ α β:
  td_measure ρ <= n ->
  langA n ρ α β <-> a⟦ ρ ⟧ α β.
Proof.
  intros. rewrite langA_measure_irrelevant; eauto.
Qed.

Lemma rty_measure_flip: forall ρ, rty_measure (flip_rty ρ) = rty_measure ρ.
Proof.
  destruct ρ; eauto.
Qed.

Lemma rtyR_measure_irrelevant_aux: forall k ρ m n e,
    rty_measure ρ <= k ->
    k <= n ->
    k <= m ->
    rtyR n ρ e <-> rtyR m ρ e.
Proof.
  induction k; destruct ρ; intros m n e Hk Hn Hm;
    split; intro H; destruct m, n;
    try solve [sinvert Hm; sinvert Hn; sinvert Hk; eauto];
    try solve [lia_tac].
  - destruct H as (HT & Hclosed & H). simpl; intuition.
    exist_tac. rewrite <- (IHk _ _ n); try lia_tac. rewrite <- (IHk _ _ n) in *; try lia_tac.
  - destruct H as (HT & Hclosed & H). simpl; intuition.
    exist_tac. rewrite (IHk _ m); try lia_tac. rewrite (IHk _ m) in *; try lia_tac.
  - destruct H as (HT & Hclosed & H). simpl; intuition.
    destruct ρ; intuition.
    + rewrite <- (IHk _ _ n) in *; try lia_tac.
    + specialize (H α β H0). exist_tac. rewrite <- (IHk _ _ n); try lia_tac.
  - destruct H as (HT & Hclosed & H). simpl; intuition.
    destruct ρ; intuition.
    + rewrite (IHk _ m) in *; try lia_tac.
    + specialize (H α β H0). exist_tac. rewrite (IHk _ m); try lia_tac.
Qed.

(* The conclusion has to be strengthened to an equivalence to get around
termination checker. *)
Lemma rtyR_measure_irrelevant m n ρ e :
  rty_measure ρ <= n ->
  rty_measure ρ <= m ->
  rtyR n ρ e <-> rtyR m ρ e.
Proof.
  intros. eapply (rtyR_measure_irrelevant_aux (rty_measure ρ)); eauto.
Qed.

Lemma rtyR_measure_irrelevant' n ρ e :
  rty_measure ρ <= n ->
  rtyR n ρ e <-> ⟦ ρ ⟧ e.
Proof.
  intros. rewrite rtyR_measure_irrelevant; eauto.
Qed.

Ltac rewrite_measure_irrelevant :=
  let t := (rewrite <- ?open_preserves_rty_measure;
            rewrite <- ?open_preserves_td_measure;
            simpl; lia) in
  match goal with
  | H : context [rtyR _ _ _] |- _ =>
      setoid_rewrite rtyR_measure_irrelevant' in H; [ | t .. ]
  | |- context [rtyR _ _ _] =>
      setoid_rewrite rtyR_measure_irrelevant'; [ | t .. ]
  | H : context [langA _ _ _ _] |- _ =>
      setoid_rewrite langA_measure_irrelevant' in H; [ | t .. ]
  | |- context [langA _ _ _ _] =>
      setoid_rewrite langA_measure_irrelevant'; [ | t .. ]
  end.

Ltac lc_solver_plus :=
  repeat (lc_solver_simp_aux || lc_basic_typing_simp_aux); eauto;
  (repeat lc_solver_plus_aux); eauto.

(* A machinery to simplify certain proofs *)
Definition tm_refine e e' :=
  (* Alternatively, we may require [∅ ⊢t e ⋮t ⌊τ⌋] in [rtyR_refine]. However, we
  would need [wf_rty] as a side-condition (or some sort of validity of [rty]),
  to make sure all components in intersection have the same erasure. This would
  introduce a large set of naming lemmas about [wf_rty] (and consequently
  everything it depends on). Annoying. *)
  (exists T, ∅ ⊢t e' ⋮t T /\ ∅ ⊢t e ⋮t T) /\
  (forall α β (v : value), α ⊧ e ↪*{ β} v -> α ⊧ e' ↪*{ β} v).

Definition value_refine (e e': value) :=
  (exists T, ∅ ⊢t e' ⋮t T /\ ∅ ⊢t e ⋮t T) /\
    (forall α β (v : value), α ⊧ e ↪*{ β} v -> α ⊧ e' ↪*{ β} v).

(* Semantic refinement preserves denotation. *)
Lemma rtyR_refine_over b ϕ (e1 e2: value) :
  value_refine e1 e2 ->
  ⟦ {: b | ϕ} ⟧ e2 ->
  ⟦ {: b | ϕ} ⟧ e1.
Proof.
  intros [Ht Hr]. intros. inversion H. simp_hyps; subst.
  simpl. intuition.
  qauto using basic_typing_tm_unique.
Qed.

Lemma tm_refine_mk_app (e1 e2: tm) (v: value) T:
  tm_refine e1 e2 ->
  lc v ->
  ∅ ⊢t mk_app_e_v e2 v ⋮t T ->
  tm_refine (mk_app_e_v e1 v) (mk_app_e_v e2 v).
Proof.
  intros. destruct H as ((Te & HTe1 & HTe2) & H).
  split.
  - exists T. intuition.
    apply mk_app_e_v_has_type_inv in H1; auto.
    simp_hyps.
    eapply mk_app_e_v_has_type; eauto. unique_basic_type. auto.
  - intros.
    rewrite reduction_mk_app_e_v_f in H2 by auto.
    simp_hyps.
    rewrite reduction_mk_app_e_v_f by auto.
    repeat eexists; eauto.
Qed.

Lemma tm_refine_tmatchb_true: forall e1 e2 T,
    ∅ ⊢t e1 ⋮t T ->
    ∅ ⊢t e2 ⋮t T ->
    tm_refine e1 (tmatchb true e1 e2).
Proof.
  split.
  - exists T. intuition.
  - intros.
    pose basic_typing_regular_tm.
    repeat (econstructor; eauto).
Qed.

Lemma tm_refine_tmatchb_false: forall e1 e2 T,
    ∅ ⊢t e1 ⋮t T ->
    ∅ ⊢t e2 ⋮t T ->
    tm_refine e2 (tmatchb false e1 e2).
Proof.
  split.
  - exists T. intuition.
  - intros.
    pose basic_typing_regular_tm.
    repeat (econstructor; eauto).
Qed.
