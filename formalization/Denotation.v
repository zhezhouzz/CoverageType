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
Inductive ctxRst: listctx rty -> epr -> Prop :=
| ctxRst0: ctxRst [] (Epr ∅ ∅ (fun σ => σ = ∅))
| ctxRst1: forall Γ σ L Σ (x: atom) b ϕ (v: value),
    ctxRst Γ (Epr σ L Σ) ->
    (* [ok_ctx] implies [ρ] is closed and valid, meaning that it does not use
    any function variables. *)
    ok_ctx (Γ ++ [(x, {: b | ϕ})]) ->
    ⟦ m{ σ }r {: b | ϕ} ⟧ v ->
    ctxRst (Γ ++ [(x, {: b | ϕ})]) (Epr (<[x := v]> σ) L Σ)
| ctxRst2: forall Γ σ L Σ (x: atom) b ϕ,
    ctxRst Γ (Epr σ L Σ) ->
    ok_ctx (Γ ++ [(x, [: b | ϕ])]) ->
    ctxRst (Γ ++ [(x, [: b | ϕ])])
      (Epr σ L (fun σ2 => exists σ1 (v: value), ⟦ m{ σ ∪ σ1 }r {: b | ϕ} ⟧ v /\ σ2 = (<[ x := v ]> σ1)))
| ctxRst3: forall Γ σ L Σ (x: atom) ρ τ (v: value),
    ctxRst Γ (Epr σ L Σ) ->
    ok_ctx (Γ ++ [(x, ρ ⇨ τ)]) ->
    ⟦ m{ σ }r (ρ ⇨ τ) ⟧ v ->
    ctxRst (Γ ++ [(x, ρ ⇨ τ)]) (Epr (<[x := v]> σ) L Σ).

(** * Properties of denotation *)

(* Lemma ctxRst_non_empty: forall Γ, (fun Γ => ok_ctx Γ -> exists P, ctxRst Γ P) Γ. *)
(* Proof. *)
(*   apply rev_ind. *)
(*   - admit. *)
(*   - intros (x & ρ) Γ HP HOk. assert (ok_ctx Γ). admit. apply HP in H. clear HP. destruct H as (P & HP). *)
(*     destruct ρ. *)
(*     + exists (fun Γv' => exists Γv (v: value), Γv' = (<[x := v]> Γv) /\ ⟦ m{ Γv }r {: b | ϕ} ⟧ v ). *)
(*       econstructor; eauto. admit. *)
(*     +  *)
(*   induction Γ. admit. *)

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

Lemma ctxRst_closed_pp Γ Γv : ctxRst Γ Γv -> closed_epr Γv.
Admitted.
(* Proof. *)
(*   unfold close_pp. unfold closed_env. *)
(*   induction 1; intros; subst; *)
(*     repeat rewrite ctxdom_app_union in *; intuition; *)
(*     try solve [apply map_Forall_empty]; *)
(*     simpl; unfold close_pp in H1; ospecialize * H1; eauto; my_set_solver. *)
(* Qed. *)

(* Lemma ctxRst_closed_env Γ p σ L Σ : ctxRst Γ (Epr σ L Σ) -> closed_env σ. *)
(* Proof. *)
(*   intros. apply ctxRst_closed_pp in H. unfold close_pp in H. ospecialize * H; eauto. *)
(*   intuition. *)
(* Qed. *)

(* Lemma ctxRst_lc Γ p Γv : *)
(*   ctxRst Γ p -> p Γv -> *)
(*   map_Forall (fun _ v => lc (treturn v)) Γv. *)
(* Proof. *)
(*   intros. apply ctxRst_closed_pp in H. unfold close_pp in H. ospecialize * H; eauto. *)
(*   intuition. *)
(* Qed. *)

Lemma ctxRst_dom Γ Γv :
  ctxRst Γ Γv ->
  ctxdom Γ ≡ eprdom Γv.
Proof.
Admitted.
(*   intros. apply ctxRst_closed_pp in H. unfold close_pp in H. ospecialize * H; eauto. *)
(*   intuition. *)
(* Qed. *)

Lemma ctxRst_ok_ctx Γ Γv :
  ctxRst Γ Γv ->
  ok_ctx Γ.
Proof.
  induction 1; eauto. econstructor.
Qed.

(* Lemma ctxRst_regular Γ p Γv: *)
(*   ctxRst Γ p -> p Γv -> ok_ctx Γ /\ ctxdom Γ ≡ dom Γv /\ closed_env Γv. *)
(* Proof. *)
(*   pose ctxRst_ok_ctx. pose ctxRst_dom. pose ctxRst_closed_env. intuition; eauto. *)
(* Qed. *)

(* Lemma ctxRst_ok_insert Γ p Γv x ρ : *)
(*   ctxRst Γ p -> p Γv -> *)
(*   ok_ctx (Γ ++ [(x, ρ)]) -> *)
(*   Γv !! x = None. *)
(* Proof. *)
(*   inversion 3; listctx_set_simpl. *)
(*   rewrite ctxRst_dom in * by eauto. *)
(*   by apply not_elem_of_dom. *)
(* Qed. *)

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
  exists c. intuition.
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
  simp_hyps; subst.
  exists v. intuition.
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
  | [H: _ |- context [rty_measure (_ ^r^ _)] ] => rewrite <- open_preserves_rty_measure
  | [H: _ |- _ <= _ ] => simpl in *; lia
  end; eauto.

Ltac exist_tac :=
  match goal with
  | [H: exists x, _ |- exists _, _ ] =>
      let x := fresh x in
      destruct H as (x & H); exists x; intuition
  end.

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
    exist_tac.
    destruct ρ1; intuition; do 2 rewrite <- (IHk _ _ n) in *; try lia_tac.
  - destruct H as (HT & Hclosed & H). simpl; intuition.
    exist_tac.
    destruct ρ1; intuition; do 2 rewrite (IHk _ m) in *; try lia_tac.
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
            simpl; lia) in
  match goal with
  | H : context [rtyR _ _ _] |- _ =>
      setoid_rewrite rtyR_measure_irrelevant' in H; [ | t .. ]
  | |- context [rtyR _ _ _] =>
      setoid_rewrite rtyR_measure_irrelevant'; [ | t .. ]
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
  (forall (v : value), e ↪* v -> e' ↪* v).

(* Definition value_refine (e e': value) := *)
(*   (exists T, ∅ ⊢t e' ⋮t T /\ ∅ ⊢t e ⋮t T) /\ *)
(*     (forall α β (v : value), α ⊧ e ↪*{ β} v -> α ⊧ e' ↪*{ β} v). *)

(* (* Semantic refinement preserves denotation. *) *)
(* Lemma rtyR_refine_over b ϕ (e1 e2: value) : *)
(*   value_refine e1 e2 -> *)
(*   ⟦ {: b | ϕ} ⟧ e2 -> *)
(*   ⟦ {: b | ϕ} ⟧ e1. *)
(* Proof. *)
(*   intros [Ht Hr]. intros. inversion H. simp_hyps; subst. *)
(*   simpl. intuition. *)
(*   qauto using basic_typing_tm_unique. *)
(* Qed. *)

Lemma tm_refine_mk_app (e1 e2 e_x: tm) T:
  tm_refine e1 e2 ->
  lc e_x ->
  ∅ ⊢t mk_app e2 e_x ⋮t T ->
  tm_refine (mk_app e1 e_x) (mk_app e2 e_x).
Proof.
  intros. destruct H as ((Te & HTe1 & HTe2) & H).
  split.
  - exists T. intuition.
    apply mk_app_has_type_inv in H1; auto.
    simp_hyps.
    eapply mk_app_has_type; eauto. unique_basic_type. auto.
  - intros.
    rewrite reduction_mk_app_iff in H2 by auto.
    simp_hyps.
    rewrite reduction_mk_app_iff by auto.
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
