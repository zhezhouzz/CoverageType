From stdpp Require Import mapset.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import RefinementTypeProp.
From CT Require Import DenotationProp.
From CT Require Import InstantiationProp.
From CT Require Import TypingProp.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import ListCtx.
Import OperationalSemantics.
Import BasicTyping.
Import Qualifier.
Import RefinementType.
Import Denotation.
Import Instantiation.
Import Typing.

(** * Main metatheoretic results *)

Ltac simpl_fv :=
  do_hyps (fun H => try match type of H with
                    | _ ∉ _ =>
                        simpl in H; rewrite ?ctxRst_dom in H by eassumption
                    end).

Lemma wf_implies_non_empty: forall Γ τ, Γ ⊢WF τ -> forall epr, ctxRst Γ epr -> exists env, eprR epr env.
Admitted.

(** Fundamental theorem for event operator typing *)
Lemma builtin_fundamental:
  well_formed_builtin_typing ->
  forall (Γ: listctx rty) (op: effop) (ρ : rty),
    Γ ⊢ op ⋮o ρ ->
    forall epr, ctxRst Γ epr -> exists Γv, eprR epr Γv -> ⟦ m{ Γv }r ρ ⟧ (value_of_op op).
Proof.
  intros HWF Γ op ρ Hop.
  sinvert Hop. apply HWF in H0.
  intros epr Hepr.
  sinvert H1. simp_hyps. ospecialize * H1; eauto.
  destruct H1 as (σ & Hσ). exists σ. intros. ospecialize * Hσ; eauto.
  rewrite msubst_fresh_rty; eauto. admit.
Admitted.

Ltac ok_solver :=
  solve [ repeat (match goal with
          | [H: ok_ctx ?Γ |- ok_ctx (?Γ ++ [(?x, ?ρ)]) ] => econstructor; eauto
          | [H: _ |- _ ∉ _ ] => my_set_solver
          end) ].

Ltac fine_solver_aux :=
  solve [repeat (match goal with
                 | [ H: _ ⊢WF _ |- fine_rty _ ] =>
                     apply closed_rty_fine in H; eauto; simpl in H;intuition; eauto
                 end)].

Ltac fine_solver :=
  match goal with
  | [H: _ |- fine_rty _ ] => fine_solver_aux
  end.

Ltac basic_typing_simp :=
  repeat match goal with
    | [H: ?Γ ⊢ _ ⋮v _ |- ⌊?Γ⌋* ⊢t _ ⋮t _ ] => apply value_typing_regular_basic_typing in H; simpl in H
    | [H: ?Γ ⊢ _ ⋮v _ |- ⌊?Γ⌋* ⊢t _ ⋮v _ ] => apply value_typing_regular_basic_typing in H; simpl in H
    | [H: ?Γ ⊢ _ ⋮t _ |- ⌊?Γ⌋* ⊢t _ ⋮t _ ] => apply tm_typing_regular_basic_typing in H; simpl in H
    | [H: ?Γ ⊢ _ ⋮t _ |- ⌊?Γ⌋* ⊢t _ ⋮v _ ] => apply tm_typing_regular_basic_typing in H; simpl in H
    | [H: (_ ⊢ _ ⋮t _) |- (_ ⊢t  _ ⋮t _) ] => apply tm_typing_regular_basic_typing in H
    end.

Ltac simp_tac :=
  closed_simp; basic_typing_simp; msubst_erase_simp; basic_typing_regular_simp.

Ltac closed_solver :=
  match goal with
  | [H: _ |- closed_rty _ ] => simp_tac
  | [H: _ |- closed_env _ ] => simp_tac
  end.

Ltac lc_solver :=
  match goal with
  | [H: _ |- lc _] => simp_tac; lc_solver_plus
  end.

Ltac misc_solver :=
  repeat msubst_simp;
  try fine_solver; try ok_solver; try closed_solver; try lc_solver.

  (* At some point the proof is very slow without marking [msubst] opaque. *)
Opaque msubst.

Ltac ctx_erase_tac :=
  repeat match goal with
  | [H: context [ ⌊_ ++ [(_, _)]⌋* ] |- _ ] => rewrite ctx_erase_app_r in H by my_set_solver
  | [H: _ |- context [ ⌊_ ++ [(_, _)]⌋* ] ] => rewrite ctx_erase_app_r by my_set_solver
  end.

Ltac restructure_typing HOrg :=
  match goal with
  | [H: ctxRst ?Γ _, HJ: _ ⊢ _ ⋮merge _ ⋮= _ |- (⟦(m{ _ }r) ?τ⟧) ((m{ _ }t) ?e)] =>
      assert (Γ ⊢ e ⋮t τ) as HOrg by (eapply TMerge in HJ; eauto)
  | [H: ctxRst ?Γ _ |- (⟦(m{ _ }r) ?τ⟧) ((m{ _ }t) ?e)] =>
      assert (Γ ⊢ e ⋮t τ) as HOrg by
        (solve [eapply TValue; eauto] ||
           solve [eapply TSub; eauto] ||
             solve [eapply TMerge; eauto] ||
               solve [eapply TLetE; eauto] ||
                   solve [eapply TAppOverParam; eauto] ||
                     solve [eapply TAppFuncParam; eauto] ||
                       solve [eapply TAppOp; eauto] ||
                         solve [eapply TMatchbTrue; eauto] ||
                           solve [eapply TMatchbFalse; eauto]
        )
  | [H: ctxRst ?Γ _ |- (⟦(m{ _ }r) ?τ⟧) (treturn (m{_}v ?e))] =>
      assert (Γ ⊢ e ⋮v τ) as HOrg by
        (solve [eapply TSubPP; eauto] ||
           solve [eapply TConst; eauto] ||
             solve [eapply TBaseVar; eauto] ||
               solve [eapply TFuncVar; eauto] ||
                 solve [eapply TFun; eauto] ||
                   solve [eapply TFix; eauto]
        )
  end.

Ltac restructure_typing_regular :=
  let HOrg := fresh "HOrg" in
  restructure_typing HOrg;
  match goal with
  | [H: ctxRst ?Γ _, HOrg: ?Γ ⊢ ?e ⋮t ?τ |- (⟦(m{ _ }r) ?τ⟧) ((m{_}t ?e))] =>
      pose (tm_typing_regular_basic_typing _ _ _ HOrg) as HBTOrg;
      pose (msubst_preserves_basic_typing_tm_empty _ _  H _ _ HBTOrg) as HBTOrgMsubst
  | [H: ctxRst ?Γ _, HOrg: ?Γ ⊢ ?e ⋮v ?τ |- (⟦(m{ _ }r) ?τ⟧) (treturn (m{_}v ?e))] =>
      pose (value_typing_regular_basic_typing _ _ _ HOrg) as HBTOrg;
      pose (msubst_preserves_basic_typing_value_empty _ _  H _ _ HBTOrg) as HBTOrgMsubst
  end.

(* Ltac auto_ctx_letbinding v_x := *)
(*   match goal with *)
(*   | [H: ∀ _, _ ∉ _ -> ∀ _, (ctxRst (?Γ ++ [(_, ?τ)]) _) -> _, H': ctxRst ?Γ ?Γv |- _ ] => *)
(*       let x := fresh "x" in *)
(*       auto_pose_fv x; repeat specialize_with x; *)
(*       assert (ctxRst (Γ ++ [(x, τ)]) (<[x:=v_x]> Γv)) as HΓv'; *)
(*       try (apply ctxRst_insert_easy; eauto; misc_solver) *)
(*   end. *)

(** Combined fundamental theorem for value typing (refinemnet types) and term
  typing (Hoare automata types) *)
Theorem fundamental_combined:
  well_formed_builtin_typing ->
  (forall (Γ: listctx rty) (v: value) (ρ: rty),
      Γ ⊢ v ⋮v ρ ->
      forall epr, ctxRst Γ epr -> exists Γv, ⟦ m{Γv}r ρ ⟧ (m{Γv}v v)) /\
    (forall (Γ: listctx rty) (e: tm) (τ: rty),
        Γ ⊢ e ⋮t τ ->
        forall epr, ctxRst Γ epr -> exists Γv, ⟦ m{ Γv }r τ ⟧ (m{ Γv }t e)).
Proof.
  pose value_reduction_any_ctx as HPureStep.
  intros HWFbuiltin.
  apply value_term_type_check_mutind.
  (* [TSubPP] *)
  - intros Γ v ρ1 ρ2 HWFρ2 _ HDρ1 Hsub Γv HΓv. specialize (HDρ1 _ HΓv).
    sinvert Hsub. simp_hyp H0. ospecialize * H1; eauto.
    apply Hsub in HDρ1; auto.
  (* [TConst] *)
  - intros Γ c HWF Γv HΓv. repeat msubst_simp. eauto using mk_eq_constant_denote_rty.
  (* [TBaseVar] *)
  - intros Γ x b ϕ Hwf Hfind Γv HΓv.
    dup_hyp HΓv (fun H => eapply ctxRst_ctxfind in H; eauto). simp_hyps.
    repeat msubst_simp. rewrite H0.
    destruct H1 as [H _].
    sinvert H. cbn in H3.
    dup_hyp H3 (fun H => apply basic_typing_base_canonical_form in H).
    simp_hyps. subst. sinvert H3.
    eauto using mk_eq_constant_denote_rty. misc_solver.
  (* [TFuncVar] *)
  - intros Γ x ρ τ Hwf Hfind Γv HΓv.
    dup_hyp HΓv (fun H => eapply ctxRst_ctxfind in H; eauto).
    { simp_hyps. repeat msubst_simp. by rewrite H0. }
    misc_solver.
  (* [TFun] *)
  - intros Γ Tx ρ e τ L HWF Ht HDe He Γv HΓv.
    restructure_typing_regular.
    repeat msubst_simp. subst.
    eapply denotation_application_lam; eauto.
    + misc_solver.
    + simpl. simp_tac; eauto.
    + eapply_eq msubst_preserves_closed_rty_empty; eauto.
      msubst_simp.
    + intros v_x Hv_x.
      auto_ctx_letbinding v_x.
      ospecialize* HDe; eauto.
      rewrite <- msubst_intro_tm in HDe by
          (eauto using ctxRst_closed_env, ctxRst_lc, rtyR_closed_value;
           simpl_fv; my_set_solver).
      rewrite <- msubst_intro_rty in HDe by
          (eauto using ctxRst_closed_env, ctxRst_lc, rtyR_closed_value;
           simpl_fv; my_set_solver).
      eauto.
  (* [TFix] *)
  - intros Γ Tx ϕ e τ T L HWF Hlam HDlam He Γv HΓv.
    restructure_typing_regular.
    repeat msubst_simp.
    eapply denotation_application_fixed; eauto.
    + misc_solver.
    + by rewrite <- rty_erase_msubst_eq.
    + assert (Γ ⊢ vfix (Tx ⤍ T) (vlam (Tx ⤍ T) e) ⋮v ({:Tx|ϕ}⇨τ))
        by eauto using value_type_check.
      eapply value_typing_regular_basic_typing in H.
      eapply msubst_preserves_basic_typing_value_empty in H; eauto.
      repeat msubst_simp.
      apply_eq H. cbn. subst. eauto.
    + eapply_eq msubst_preserves_closed_rty_empty; eauto.
      repeat msubst_simp.
    + intros v_x Hv_x.
      auto_ctx_letbinding v_x.
      ospecialize* HDlam; eauto.
      rewrite <- msubst_intro_value in HDlam by
          (eauto using ctxRst_closed_env, ctxRst_lc, rtyR_closed_value;
           simpl_fv; my_set_solver).
      repeat msubst_simp.
      rewrite <- msubst_intro_rty in HDlam by
          (eauto using ctxRst_closed_env, ctxRst_lc, rtyR_closed_value;
           simpl_fv; my_set_solver).
      rewrite msubst_insert_fresh_rty in HDlam by
          (eauto using ctxRst_closed_env, rtyR_closed_value; simpl_fv; my_set_solver).
      rewrite_msubst msubst_qualifier in HDlam.
      rewrite msubst_insert_fresh_qualifier in HDlam by
          (eauto using ctxRst_closed_env, rtyR_closed_value; simpl_fv; my_set_solver).
      apply_eq HDlam.
      simpl. repeat msubst_simp.
      clear. simplify_map_eq. eauto.
  (* [TEPur] *)
  - intros Γ v ρ HWF Hv HDv Γv HΓv. specialize (HDv _ HΓv).
    restructure_typing_regular.
    repeat msubst_simp.
    split; [| split].
    + simp_tac; eauto.
    + eapply_eq msubst_preserves_closed_rty_empty; eauto.
      repeat msubst_simp.
    + finerty_destruct ρ; intros.
      * simpl in *. simp_hyps; subst. repeat auto_apply.
        intros. apply value_reduction_any_ctx. misc_solver.
      * exists ((m{Γv}v) v). simpl in *. simp_hyps; subst. intuition.
        { exists ((m{Γv}v) v). intuition. apply value_reduction_any_ctx. misc_solver. }
        { apply value_reduction_any_ctx. misc_solver. }
  (* [TSub] *)
  - intros Γ e τ1 τ2 HWFτ2 _ HDτ1 Hsub Γv HΓv. specialize (HDτ1 _ HΓv).
    apply Hsub in HDτ1; auto.
  (* [TMerge] *)
  - unfold join. intros Γ e τ1 τ2 τ3 HWFτ3 _ HDτ1 _ HDτ2 (_ & _ & _ & _ & Hjoin) Γv HΓv.
    specialize (HDτ1 _ HΓv). specialize (HDτ2 _ HΓv).
    rewrite Hjoin; eauto.
  (* [TLetE] *)
  - intros Γ e_x e ρ1 A ρ' B L HTe_x HDe_x HWF HTe HDe Γv HΓv.
    restructure_typing_regular.
    repeat msubst_simp.
    eapply denotation_application_tlete; simp_tac.
    + ospecialize* HDe; eauto. repeat msubst_simp.
    + intros v_x Hv_x.
      auto_ctx_letbinding v_x.
      by (apply tm_typing_regular_wf in HTe; finerty_destruct ρ1; simpl; eauto).
      ospecialize* HDe_x; eauto.
      rewrite msubst_insert_fresh_rty in HDe_x. repeat msubst_simp.
      rewrite open_rec_lc_rty.
      erewrite msubst_intro_tm; eauto.
      all: rtyR_regular_simp; misc_solver.
  (* [TApp] *)
  - intros Γ v1 v2 e ρ1 ρ2 A ρ B L HTe HDe HWF HTv2 HDv2 HTv1 HDv1 Γv HΓv.
    restructure_typing_regular.
    assert (lc v2) as Hlcv2. {
      apply value_typing_regular_basic_typing in HTv2.
      lc_solver_plus.
    }
    assert (⌊ Γ ⌋* ⊢t (mk_app_e_v v1 v2) ⋮t ⌊ ρ2 ⌋) as HBTMkApp. {
      eapply mk_app_e_v_has_type; basic_typing_simp; eauto.
    }
    ospecialize* HDv1; eauto. ospecialize* HDv2; eauto. repeat msubst_simp.
    rewrite msubst_open_td by simp_tac. repeat msubst_simp.
    eapply denotation_application_tletapp; eauto.
    all: try solve [simp_tac].
    + eapply_eq msubst_preserves_closed_rty_empty; eauto.
      repeat msubst_simp. rewrite msubst_open_td; simp_tac.
    + intros v_x Hv_x.
      auto_ctx_letbinding v_x.
      by (rewrite msubst_open_rty; simp_tac).
      by (apply value_typing_regular_wf in HTv1;
          rewrite closed_rty_arr in HTv1;
          finerty_destruct ρ2; simpl in *; intuition).
      ospecialize* HDe; eauto.
      rewrite msubst_insert_fresh_rty in HDe. repeat msubst_simp.
      rewrite open_rec_lc_rty.
      erewrite msubst_intro_tm; eauto.
      all: rtyR_regular_simp; misc_solver.
  (* [TEOpApp] *)
  - intros Γ op v2 e ρ2 b1 ϕ1 A1 τ2 A2 L HTe HDe HWF HTv2 HDv2 HTop Γv HΓv.
    restructure_typing_regular.
    assert (lc v2) as Hlcv2. {
      apply value_typing_regular_basic_typing in HTv2.
      lc_solver_plus.
    }
    sinvert HTop. apply HWFbuiltin in H0. destruct H1 as (_ & _ & Hsub).
    ospecialize* (Hsub _ HΓv).
    { assert (closed_rty ∅ ρ_op) as HClosedOp by simp_tac. simp_tac. }
    repeat msubst_simp.
    rewrite msubst_open_td by simp_tac. repeat msubst_simp.
    eapply denotation_application_tletopapp; eauto.
    all: try solve [simp_tac].
    + eapply msubst_preserves_closed_rty_empty in HWF; eauto. repeat msubst_simp.
      rewrite msubst_open_td in HWF; eauto; simp_tac.
    + intros v_x Hv_x.
      auto_ctx_letbinding v_x.
      { rewrite msubst_open_rty; simp_tac. }
      ospecialize* HDe; eauto.
      rewrite msubst_insert_fresh_rty in HDe. repeat msubst_simp.
      rewrite open_rec_lc_rty.
      erewrite msubst_intro_tm; eauto.
      all: rtyR_regular_simp; misc_solver.
  (* [TMatchb] *)
  - intros Γ v e1 e2 ϕ τ L HWF HTv HDv HTe1 HDe1 HTe2 HDe2 Γv HΓv.
    restructure_typing_regular.
    assert (is_tm_rty τ) as HisTmRty by (eapply value_tm_typing_regular_is_tm_rty; eauto).
    auto_pose_fv x. repeat specialize_with x.
    ospecialize* HDv; eauto.
    repeat msubst_simp.
    assert (exists (b : bool), m{Γv}v v = b) as [b He] by
        qauto using value_typing_regular_basic_typing,
                    msubst_preserves_basic_typing_value_empty,
                    basic_typing_bool_canonical_form.
    rewrite He in *.
    assert (ctxRst
              (Γ ++ [(x, {:TBool|(b0:c=b) & ((b0:v=v) & ϕ)})])
              (<[x:=vconst b]>Γv)) as HΓv'. {
      apply ctxRst_insert_easy; eauto. my_set_solver.
      repeat msubst_simp.
      repeat apply denote_base_rty_qualifier_and; eauto.
      apply_eq mk_eq_constant_over_denote_rty. clear - HΓv.
      rewrite_msubst msubst_qualifier. simpl. repeat msubst_simp.
      apply_eq mk_eq_constant_over_denote_rty. clear - He HΓv.
      rewrite_msubst msubst_qualifier. simpl. rewrite He. repeat msubst_simp.
      fine_solver.
    }
    destruct b.
    + ospecialize* HDe1; eauto.
      rewrite msubst_insert_fresh_tm in HDe1 by
          (eauto using ctxRst_closed_env; simpl_fv; my_set_solver).
      rewrite msubst_insert_fresh_rty in HDe1 by
          (eauto using ctxRst_closed_env; simpl_fv; my_set_solver).
      eapply rtyR_refine; eauto. misc_solver.
      sinvert HBTOrgMsubst. eapply tm_refine_tmatchb_true; eauto.
    + ospecialize* HDe2; eauto.
      rewrite msubst_insert_fresh_tm in HDe2 by
          (eauto using ctxRst_closed_env; simpl_fv; my_set_solver).
      rewrite msubst_insert_fresh_rty in HDe2 by
          (eauto using ctxRst_closed_env; simpl_fv; my_set_solver).
      eapply rtyR_refine; eauto. misc_solver.
      sinvert HBTOrgMsubst. eapply tm_refine_tmatchb_false; eauto.
Qed.

(** Fundamental theorem for value typing *)
Theorem fundamental_value:
  well_formed_builtin_typing ->
  forall (Γ: listctx rty) (v: value) (ρ: rty),
    Γ ⊢ v ⋮v ρ ->
    forall Γv, ctxRst Γ Γv -> ⟦ m{Γv}r ρ ⟧ (m{Γv}v v).
Proof.
  qauto using fundamental_combined.
Qed.

(** Fundamental theorem (Theorem 4.8) *)
Theorem fundamental:
  well_formed_builtin_typing ->
  forall (Γ: listctx rty) (e: tm) (τ: rty),
    Γ ⊢ e ⋮t τ ->
    forall σ, ctxRst Γ σ -> ⟦ m{ σ }r τ ⟧ (m{ σ }t e).
Proof.
  qauto using fundamental_combined.
Qed.

Transparent msubst.

(** A general type soundness theorem *)
Corollary soundness :
  well_formed_builtin_typing ->
  forall (e : tm) b (ϕ : qualifier) (A : transducer),
    [] ⊢ e ⋮t ([:b|ϕ]!<[ A ]>) ->
    forall (v : value) α β,
      ⟦ {:b|ϕ} ⟧ v ->
      a⟦ A ^a^ v ⟧ α β ->
      α ⊧ e ↪*{ β } v.
Proof.
  intros HWF * HT * HDα Hstepv.
  eapply fundamental in HT; eauto using ctxRst.
  unfold msubst in HT. rewrite !map_fold_empty in HT.
  qauto using HT.
Qed.

Print Assumptions soundness.
