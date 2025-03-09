From stdpp Require Import mapset.
From stdpp Require Import natmap.
From Coq.Program Require Import Wf.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import RefinementTypeProp.
From CT Require Import InstantiationProp.
From CT Require Import Denotation.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import ListCtx.
Import OperationalSemantics.
Import BasicTyping.
Import Qualifier.
Import RefinementType.
Import Instantiation.
Import Denotation.

Ltac rtyR_regular_simp :=
  (repeat match goal with
     (* | [H: ctxRst _ _ |- lc _ ] => apply ctxRst_regular in H; simp_hyp H *)
     (* | [H: ctxRst _ _ |- closed_env _ ] => apply ctxRst_regular in H; simp_hyp H *)
     (* | [H: ctxRst _ _ |- ok_ctx _ ] => apply ctxRst_regular in H; simp_hyp H; eauto *)
     (* | [H: ctxRst _ _ |- _ ∉ _ ] => apply ctxRst_regular in H; simp_hyp H; eauto *)
     (* | [H: ctxRst _ ?Γv |- map_Forall _ ?Γv] => apply ctxRst_lc in H; eauto *)
     | [H: rtyR _ _ _ |- lc _ ] => apply rtyR_typed_closed in H; simp_hyp H
     | [H: rtyR _ _ _ |- lc_rty _ ] => apply rtyR_typed_closed in H; simp_hyp H
     | [H: rtyR _ _ _ |- closed_value _ ] => apply rtyR_closed_value in H; eauto; simp_hyp H
     | [H: rtyR _ _ _ |- closed_tm _ ] => apply rtyR_closed_tm in H; eauto; simp_hyp H
     | [H: rtyR _ _ _ |- _ ⊢t _ ⋮v _ ] => apply rtyR_typed_closed in H; simp_hyp H
     | [H: rtyR _ _ _ |- _ ⊢t _ ⋮t _ ] => apply rtyR_typed_closed in H; simp_hyp H
     | [H: closed_rty _ _ |- lc_rty _ ] => destruct H; eauto
     | [H: _ ≡ _ |- _ ∉ _ ] => rewrite H in *
     end); basic_typing_regular_simp.

(* Ltac is_tm_rty_tac := *)
(*   match goal with *)
(*   | [H: _ |- is_tm_rty _ ] => *)
(*       (repeat match goal with *)
(*          | [H: _ |- is_tm_rty (_ ^r^ _) ] => rewrite is_tm_rty_open; eauto *)
(*          | [H: _ |- is_tm_rty ((m{ _ }r) _) ] => rewrite is_tm_rty_msubst; eauto *)
(*          | [H: _ |- is_tm_rty (({ _ := _ }r) _) ] => rewrite is_tm_rty_subst; eauto *)
(*          | [H: closed_rty _ (_ ⇨ ?τ) |- is_tm_rty ?τ] => eauto using is_tm_rty_retrty *)
(*          end) *)
(*   end. *)

Lemma rtyR_refine_aux n: forall τ e1 e2,
    rty_measure τ <= n ->
    is_coverage_rty τ ->
    tm_refine e1 e2 ->
    rtyR n τ e1 ->
    rtyR n τ e2.
Proof.
  induction n; intros τ e1 e2 Hm Hunder [Ht Hr] H; simpl in *;
    destruct τ; simpl in *; eauto; try easy.
  qauto using basic_typing_tm_unique.
  intuition.
  - qauto using basic_typing_tm_unique.
  - destruct H2 as (v & Hv & Hvv); subst.
    exists v. intuition.
  (*   eapply IHn; eauto. *)
  (*   + repeat rewrite_measure_irrelevant. *)
  (*     rewrite <- open_preserves_rty_measure. lia. *)
  (*   + is_tm_rty_tac. *)
  (*   + simp_hyps. unique_basic_type. *)
  (*     eapply tm_refine_mk_app; eauto. *)
  (*     * split; eauto. *)
  (*     * rtyR_regular_simp. *)
  (*     * eapply mk_app_e_v_has_type; eauto. *)
  (*       rtyR_regular_simp. basic_typing_solver. *)
  (* - intuition. qauto using basic_typing_tm_unique. *)
  (*   destruct τ; eauto. *)
  (*   intros. edestruct H2 as (v & Hv & Hvv); eauto. *)
Qed.

Lemma rtyR_refine: forall τ e1 e2,
    is_coverage_rty τ ->
    tm_refine e1 e2 ->
    ⟦ τ ⟧ e1 ->
    ⟦ τ ⟧ e2.
Proof.
  pose rtyR_refine_aux. eauto.
Qed.

Lemma denot_const_overrty (c: constant):
  forall (T: base_ty) ϕ,
    closed_rty ∅ {:T|ϕ} -> ∅ ⊢t c ⋮t T -> denote_qualifier (ϕ ^q^ c) -> (⟦{:T|ϕ}⟧) c.
Proof.
  intros.
  split; [| split]; eauto.
Qed.
