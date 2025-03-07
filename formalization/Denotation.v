From stdpp Require Import mapset.
From stdpp Require Import natmap.
From Coq.Program Require Import Wf.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import TransducerProp.
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
Import Transducer.
Import RefinementType.
Import Trace.

(** This file defines type denotations in λᴱ (Fig. 7). *)

(** Trace language (Fig. 7) *)

(** Well-formedness of a single event *)
Definition valid_evop 'ev{op ~ argv := retv} :=
  ∅ ⊢t argv ⋮v TNat /\ ∅ ⊢t retv ⋮v ret_ty_of_op op.

(** Well-formedness of traces (Trᵂᶠ in Fig. 7) *)
Definition valid_trace := Forall valid_evop.

(** Transducer denotation *)

Fixpoint langA (gas: nat) (a: transducer) (α: list evop) (β: list evop) : Prop :=
  match gas with
  | 0 => False
  | S gas' =>
      closed_td ∅ a /\ valid_trace α /\ valid_trace β /\
        (match a with
         | tdId => α = β
         | ⟨ op | ϕ ⟩/id =>
             exists (c_arg c_ret: constant),
             denote_qualifier ({0 ~q> c_ret} ({1 ~q> c_arg} ϕ)) /\
               α = [ev{op ~ c_arg := c_ret}] /\
               β = [ev{op ~ c_arg := c_ret}]
         | ⟨ op1 | ϕ ⟩/⟨ op2 | v_arg | v_ret ⟩ =>
             exists (c_arg c_ret c_arg' c_ret': constant),
             v_arg = c_arg' -> v_ret = c_ret' ->
             denote_qualifier ({0 ~q> c_ret} ({1 ~q> c_arg} ϕ)) /\
               α = [ev{op1 ~ c_arg := c_ret}] /\
               β = [ev{op2 ~ c_arg' := c_ret'}]
         | a1 ○ a2 => exists γ, langA gas' a1 α γ /\ langA gas' a2 γ β
         | tdUnion a1 a2 => langA gas' a1 α β ∨ langA gas' a2 α β
         | tdEx b ϕ a =>
             exists c, ∅ ⊢t c ⋮v b /\ denote_qualifier ({0 ~q> c} ϕ) /\ langA gas' (a ^a^ c) α β
         | tdExArr T1 T2 a => langA gas' a α β
         end)
  end.

Notation "'a⟦' a '⟧' " := (langA (td_measure a) a) (at level 20, format "a⟦ a ⟧", a constr).

(** Type Denotation *)

(* This measure function is used to guarantee termination of the denotation.
Instead of addtion, we can also use [max] for the subterms. *)
Fixpoint rty_measure (ρ: rty) : nat :=
  match ρ with
  | rtyOver _ _ | rtyUnder _ _ => 1
  | ρ ⇨ τ => 1 + rty_measure ρ + rty_measure τ
  | ρ !<[ _ ]> => 1 + rty_measure ρ
  end.

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
        | {: b | ϕ} =>
            forall (v: value), (forall α, α ⊧ e ↪*{α} v) -> denote_qualifier (ϕ ^q^ v)
        | [: b | ϕ] =>
            forall (v: value), denote_qualifier (ϕ ^q^ v) -> (forall α, α ⊧ e ↪*{α} v)
        | ρx ⇨ τ =>
            exists (v: value), (forall α, α ⊧ e ↪*{α} v) /\
                            (forall (v_x: value), rtyR gas' ρx v_x -> rtyR gas' (τ ^r^ v_x) (mk_app_e_v e v_x))
        | ρ !<[ a ]> =>
            match ρ with
            | {: _ | _} | _ !<[ _ ]> => False
            | [: b | ϕ] =>
                forall α β (v: value),
                  a⟦ (a ^a^ v) ⟧ α β -> rtyR gas' {: b | ϕ} v -> α ⊧ e ↪*{β} v
            | ρx ⇨ τ =>
                forall α β, a⟦ a ⟧ α β ->
                            exists (v: value), rtyR gas' (ρx ⇨ τ) v /\ α ⊧ e ↪*{β} v
            end
        end
  end.

Notation "'⟦' τ '⟧' " := (rtyR (rty_measure τ) τ) (at level 20, format "⟦ τ ⟧", τ constr).

(** Context denotation (Fig. 7), defined as an inductive relation instead of a
  [Prop]-valued function. *)
Inductive ctxRst: listctx rty -> env -> Prop :=
| ctxRst0: ctxRst [] ∅
| ctxRst1: forall Γ env (x: atom) ρ (v: value),
    ctxRst Γ env ->
    (* [ok_ctx] implies [ρ] is closed and valid, meaning that it does not use
    any function variables. *)
    ok_ctx (Γ ++ [(x, ρ)]) ->
    ⟦ m{ env }r ρ ⟧ v ->
    ctxRst (Γ ++ [(x, ρ)]) (<[ x := v ]> env).

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

Lemma rty_measure_gt_0 ρ : rty_measure ρ > 0.
Proof.
  induction ρ; simpl; lia.
Qed.

Lemma rty_measure_S ρ : exists n, rty_measure ρ = S n.
Proof.
  destruct (Nat.lt_exists_pred 0 (rty_measure ρ)).
  pose proof (rty_measure_gt_0 ρ). lia.
  intuition eauto.
Qed.

Lemma open_preserves_rty_measure ρ: forall k t,
    rty_measure ρ = rty_measure ({k ~r> t} ρ).
Proof.
  induction ρ; simpl; eauto.
Qed.

Lemma subst_preserves_rty_measure ρ: forall x t,
    rty_measure ρ = rty_measure ({x:=t}r ρ).
Proof.
  induction ρ; simpl; eauto.
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
