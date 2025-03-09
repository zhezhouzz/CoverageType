From stdpp Require Import mapset.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import RefinementTypeProp.
From CT Require Import DenotationProp.
From CT Require Import InstantiationProp.
From CT Require Import Typing.

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

Ltac closed_simp :=
  (repeat match goal with
     | [H: ⟦ _ ⟧ _ |- closed_rty _ _ ] => apply rtyR_typed_closed in H; simp_hyp H
     (* | [H: ctxRst _ ?Γv |- closed_env ?Γv] => eapply ctxRst_closed_env; eauto *)
     (* | [H: ctxRst _ ?Γv |- map_Forall _ ?Γv] => eapply ctxRst_lc in H; eauto *)
     | [H: _ ⊢ _ ⋮t _ |- closed_rty _ _ ] => apply tm_typing_regular_wf in H
     | [H: _ ⊢ _ ⋮v _ |- closed_rty _ _ ] => apply value_typing_regular_wf in H
     (* | [H: ?Γ ⊢WF _ , H': ctxRst ?Γ _ |- closed_rty _ _ ] => *)
     (*     eapply (msubst_preserves_closed_rty_empty _ _ _ H') in H; eauto *)
     | [H: closed_rty ∅ ?τ |- context [ (m{ _ }r) ?τ] ] =>
         rewrite msubst_fresh_rty by solve [sinvert H; set_solver]
     | [H: closed_rty ∅ ?τ, H': context [ (m{ _ }r) ?τ] |- _ ] =>
         rewrite msubst_fresh_rty in H' by solve [sinvert H; set_solver]
     end); repeat msubst_simp.

(* Ltac finerty_destruct τ := *)
(*   destruct τ; repeat msubst_simp; *)
(*   try match goal with *)
(*   | [H: closed_rty ∅ ({: _ | _ }!<[ _ ]>) |- _ ] => *)
(*       apply closed_rty_fine in H; simpl in H; intuition *)
(*   | [H: closed_rty ∅ ((_ !<[ _ ]> )!<[ _ ]>) |- _ ] => *)
(*       apply closed_rty_fine in H; simpl in H; intuition *)
(*   end. *)

(** Convert an event operator to a value:
  [op] is [fun x => leteffop y = op x in y] *)
Definition value_of_op op : value :=
  vlam TNat (tleteffop op (vbvar 0) (vbvar 0)).

(** Well-formed built-in operator typing context (Definition 4.7) *)
(* We simply treat the event operator as a value. This is equivalent to the
definition in the paper (if we expand the denotation of this value). *)
Definition well_formed_builtin_typing :=
  forall op ρ,
    builtin_typing_relation op ρ ->
    ⟦ ρ ⟧ (value_of_op op).

Lemma msubst_value_of_op Γv op :
  m{Γv}v (value_of_op op) = value_of_op op.
Proof.
  rewrite msubst_fresh_value. eauto.
  my_set_solver.
Qed.

Lemma value_of_op_regular_basic_typing op:
  ∅ ⊢t value_of_op op ⋮v ty_of_op op.
Proof.
  econstructor.
  simpl. instantiate (1:=∅). intros.
  econstructor. econstructor. simplify_map_eq. reflexivity. reflexivity.
  instantiate_atom_listctx.
  simpl. econstructor. econstructor. simplify_map_eq. reflexivity.
Qed.

(* Lemma denotation_application_tlete ρ_x A ρ B e_x e: *)
(*   closed_rty ∅ (ρ !<[ (ex_phi_to_td ρ_x A) ○ B ]>) -> *)
(*   ∅ ⊢t tlete e_x e ⋮t ⌊ρ⌋ -> *)
(*   ⟦ ρ_x!<[A]> ⟧ e_x -> *)
(*   (forall (v_x : value), ⟦ flip_rty ρ_x ⟧ v_x -> ⟦ (ρ !<[ B ]>) ^r^ v_x⟧ (e ^t^ v_x)) -> *)
(*   (⟦ ρ !<[ (ex_phi_to_td ρ_x A) ○ B ]> ⟧) (tlete e_x e). *)
(* Proof. *)
(*   intros Hclosed2 HTe He_x He. *)
(*   assert (closed_rty ∅ (ρ_x!<[A]>)) as Hclosed1 by solve [simpl in *; intuition]. *)
(*   split; [| split]; eauto. *)
(*   finerty_destruct ρ. *)
(*   - intros α β v H HDv. simpl td_open in H. *)
(*     rewrite langA_comp_spec in H. destruct H as (α' & Hα & Hβ). *)
(*     finerty_destruct ρ_x; simpl flip_rty in *; simpl ex_phi_to_td in *; *)
(*       rewrite open_rec_lc_td in Hα by solve [lc_simpl; sinvert H0; auto_exists_L]. *)
(*     + rewrite langA_ex_spec in Hα. destruct Hα as (v_x & Hv_x & Hα). *)
(*       specialize (He v_x Hv_x). *)
(*       destruct He_x as (HTe_x & Hclosed3 & He_x). *)
(*       specialize (He_x α α' v_x Hα Hv_x). *)
(*       rewrite open_rec_lc_rty in He by (lc_simpl; rewrite lc_rty_td; intuition; lc_simpl; eauto). *)
(*       destruct He as (HTe' & Hclosed4 & He). *)
(*       specialize (He α' β v Hβ HDv). *)
(*       eapply reduction_tlete'; eauto. lc_solver_plus. *)
(*     + rewrite denotation_tdExArr_same in Hα. *)
(*       destruct He_x as (HTe_x & Hclosed3 & He_x). *)
(*       ospecialize (He_x α α' _); eauto. destruct He_x as (v_x & HMeasure2 & Hv_x). *)
(*       ospecialize (He v_x _); eauto. *)
(*       rewrite open_rec_lc_rty in He by (lc_simpl; rewrite lc_rty_td; intuition; lc_simpl; eauto). *)
(*       destruct He as (HTe' & Hclosed4 & He). *)
(*       ospecialize (He α' β v _ _); eauto. *)
(*       eapply reduction_tlete'; eauto. lc_solver_plus. *)
(*   - intros α β H. *)
(*     finerty_destruct ρ_x; simpl flip_rty in *; simpl ex_phi_to_td in *; *)
(*       rewrite langA_comp_spec in H; destruct H as (α' & Hα & Hβ). *)
(*     + rewrite langA_ex_spec in Hα. destruct Hα as (v_x & Hv_x & Hα). *)
(*       specialize (He v_x Hv_x). *)
(*       destruct He_x as (HTe_x & Hclosed3 & He_x). *)
(*       ospecialize (He_x α α' v_x _ _); eauto. *)
(*       rewrite open_rec_lc_rty in He by (lc_simpl; rewrite lc_rty_td; intuition; lc_simpl; eauto). *)
(*       destruct He as (HTe' & Hclosed4 & He). *)
(*       specialize (He α' β Hβ). destruct He as (v & Hv & He). *)
(*       exists v. split; auto. *)
(*       eapply reduction_tlete'; eauto. lc_solver_plus. *)
(*     + rewrite denotation_tdExArr_same in Hα. *)
(*       destruct He_x as (HTe_x & Hclosed3 & He_x). *)
(*       ospecialize * He_x; eauto. *)
(*       destruct He_x as (v_x & Hmeasure2 & Hv_x). *)
(*       ospecialize * He; eauto. *)
(*       rewrite open_rec_lc_rty in He by (lc_simpl; rewrite lc_rty_td; intuition; lc_simpl; eauto). *)
(*       destruct He as (HTe' & Hclosed4 & He). *)
(*       specialize (He α' β Hβ). destruct He as (v & Hv & He). *)
(*       exists v. split; auto. *)
(*       eapply reduction_tlete'; eauto. lc_solver_plus. *)
(* Qed. *)

Ltac is_coverage_rty_tac :=
  repeat match goal with
    | [H: _ |- is_coverage_rty (_ ^r^ _) ] => rewrite is_coverage_rty_open; eauto
    | [H: _ |- is_coverage_rty ((m{ _ }r) _) ] => rewrite is_coverage_rty_msubst; eauto
    | [H: _ |- is_coverage_rty (({ _ := _ }r) _) ] => rewrite is_coverage_rty_subst; eauto
    end.

Ltac unique_basic_type :=
  repeat match goal with
  | [ H: ?g ⊢t ?e ⋮t ?T, H': ?g ⊢t ?e ⋮t ?T |- _ ] => clear H'
  | [ H: ?g ⊢t ?e ⋮v ?T, H': ?g ⊢t ?e ⋮v ?T |- _ ] => clear H'
  | [H: _ ⤍ _ = ⌊ _ ⇨ _ ⌋ |- _ ] => sinvert H
  | [ H: ?g ⊢t ?e ⋮t ?T, H': ?g ⊢t ?e ⋮t ?T' |- _ ] =>
      assert (T = T') by eauto using basic_typing_tm_unique; subst
  | [ H: ?g ⊢t ?e ⋮v ?T, H': ?g ⊢t ?e ⋮v ?T' |- _ ] =>
      assert (T = T') by eauto using basic_typing_value_unique; subst
  | [ H: ?g ⊢t ?e ⋮v ?T, H': ?g ⊢t (treturn ?e) ⋮t ?T' |- _ ] =>
      sinvert H';
      assert (T = T') by eauto using basic_typing_value_unique; subst
  end.

Ltac simp_for_basic_typing :=
  (repeat match goal with
  | [H: rtyR _ _ _ |- tm_has_type _ _ _ ] =>
      apply rtyR_typed_closed in H; simp_hyp H; eauto
  | [H: rtyR _ _ _ |- value_has_type _ _ _ ] =>
      apply rtyR_typed_closed in H ; simp_hyp H; eauto
     end); unique_basic_type.

(* Lemma denotation_application_tletapp ρ1 τ2 A ρ B (v1 v2: value) e: *)
(*   closed_rty ∅ (ρ !<[ ((ex_phi_to_td τ2 A) ^a^ v2) ○ B ]>) -> *)
(*   ∅ ⊢t tletapp v1 v2 e ⋮t ⌊ρ⌋ -> *)
(*   ⟦ρ1⟧ v2 -> *)
(*   ⟦ρ1⇨(τ2!<[A]>)⟧ v1 -> *)
(*   (forall (v_x : value), ⟦ (flip_rty τ2) ^r^ v2 ⟧ v_x -> ⟦ (ρ !<[ B ]>) ^r^ v_x⟧ (e ^t^ v_x)) -> *)
(*   ⟦ ρ !<[ ((ex_phi_to_td τ2 A) ^a^ v2) ○ B ]> ⟧ (tletapp v1 v2 e). *)
(* Proof. *)
(*   intros. *)
(*   assert (∅ ⊢t mk_app v1 v2 ⋮t ⌊ τ2 ⌋). *)
(*   { sinvert H0. simp_for_basic_typing. *)
(*     eapply mk_app_has_type; simp_for_basic_typing; eauto. } *)
(*   eapply rtyR_refine with (e1 := tlete (mk_app v1 v2) e). is_coverage_rty_tac. *)
(*   { sinvert H0. simp_for_basic_typing. *)
(*     econstructor. *)
(*     - eexists; intuition; simp_for_basic_typing; eauto. *)
(*     - intros. rewrite reduction_tlete_iff in H0. simp_hyp H0. *)
(*       rewrite reduction_tletapp_iff. intuition. lc_solver_plus. *)
(*       do 2 eexists; intuition; eauto. } *)
(*   assert (fine_rty (τ2!<[A]>)) as Hfine by *)
(*       (apply rtyR_typed_closed in H2; rewrite closed_rty_arr in H2; simpl in *; intuition). *)
(*   rewrite ex_phi_to_td_open by (simpl in Hfine; intuition). *)
(*   rewrite ex_phi_to_td_open in H by (simpl in Hfine; intuition). *)
(*   setoid_rewrite flip_rty_open in H3. *)
(*   apply denotation_application_tlete; eauto. *)
(*   - sinvert H0. simp_for_basic_typing. *)
(*     assert (∅ ⊢t mk_app v1 v2 ⋮t ⌊ τ2 ⌋). *)
(*     { eapply mk_app_has_type; simp_for_basic_typing; eauto. } *)
(*     auto_exists_L. *)
(*   - simpl in H2. simp_hyp H2. ospecialize (H8 v2 _); *)
(*       repeat rewrite_measure_irrelevant; eauto. *)
(*     rewrite rtyR_measure_irrelevant' in H8; eauto. simpl. *)
(*     setoid_rewrite <- open_preserves_rty_measure. lia. *)
(* Qed. *)

Lemma reduction_tleteffop_op_iff: forall op (c c': constant),
    mk_app (value_of_op op) c ↪* c' <-> ⇓{op~c}{c'}.
Proof.
  split; intros.
  - rewrite reduction_mk_app_iff in H; eauto. simp_hyps.
    apply value_reduction_refl in H. sinvert H.
    unfold value_of_op in H2.
    rewrite reduction_tletapp_iff in H2; simp_hyps; simpl in *; value_reduction_simp.
    sinvert H1. sinvert H0. simpl in H2.
    rewrite reduction_tlete_iff in H2; simp_hyps; simpl in *; value_reduction_simp.
    sinvert H0. sinvert H1.
    simpl in *; value_reduction_simp. eauto.
  - unfold value_of_op.
    rewrite reduction_mk_app_iff; eauto.
    exists (vlam TNat (tleteffop op (vbvar 0) (vbvar 0))), c. intuition; eauto.
    econstructor. admit. admit.
Admitted.

(* Lemma denotation_application_tletopapp ρ1 b2 ϕ2 A ρ B op (v2: value) e: *)
(*   closed_rty ∅ (ρ !<[ ((ex_phi_to_td [:b2|ϕ2] A) ^a^ v2) ○ B ]>) -> *)
(*   ∅ ⊢t tleteffop op v2 e ⋮t ⌊ρ⌋ -> *)
(*   ⟦ρ1⟧ v2 -> *)
(*   ⟦ρ1⇨[:b2|ϕ2]!<[A]>⟧ (value_of_op op) -> *)
(*   (forall (v_x : value), ⟦ (flip_rty [:b2|ϕ2]) ^r^ v2 ⟧ v_x -> ⟦ (ρ !<[ B ]>) ^r^ v_x⟧ (e ^t^ v_x)) -> *)
(*   ⟦ ρ !<[ ((ex_phi_to_td [:b2|ϕ2] A) ^a^ v2) ○ B ]> ⟧ (tleteffop op v2 e). *)
(* Proof. *)
(*   intros. *)
(*   sinvert H0. *)
(*   assert (T1 ⤍ Tx = ⌊ρ1⌋ ⤍ b2). { *)
(*     apply rtyR_typed_closed in H1; simp_hyp H1; eauto. *)
(*     apply rtyR_typed_closed in H2; simp_hyp H2; eauto. *)
(*     pose (value_of_op_regular_basic_typing op) as HZ. rewrite H10 in HZ. *)
(*     sinvert H2. *)
(*     eapply basic_typing_value_unique; eauto. *)
(*   } *)
(*   sinvert H0; subst. *)
(*   assert (∅ ⊢t mk_app (value_of_op op) v2 ⋮t b2). *)
(*   { eapply mk_app_has_type; eauto. *)
(*     rewrite <- H10. econstructor. apply value_of_op_regular_basic_typing. } *)
(*   eapply rtyR_refine with (e1 := tlete (mk_app (value_of_op op) v2) e). is_coverage_rty_tac. *)
(*   { econstructor. *)
(*     - eexists; intuition; eauto. *)
(*     - intros. rewrite reduction_tlete_iff in H4. simp_hyp H4. *)
(*       rewrite reduction_tleteffop_iff. intuition. *)
(*       sinvert H8. assert (∅ ⊢t v_x ⋮t b2). { *)
(*         eapply multi_preservation; eauto. *)
(*       } sinvert H6. sinvert H13. *)
(*       rewrite reduction_tleteffop_op_iff in H7. *)
(*       exists c. exists c0. exists βx; intuition. *)
(*       all: my_set_solver. *)
(*   } *)
(*   rewrite ex_phi_to_td_open by (simpl in *; intuition). *)
(*   rewrite ex_phi_to_td_open in H by (simpl in *; intuition). *)
(*   setoid_rewrite flip_rty_open in H3. *)
(*   apply denotation_application_tlete; eauto. *)
(*   - simpl in H2. simp_hyp H2. ospecialize (H9 v2 _); *)
(*       repeat rewrite_measure_irrelevant; eauto. *)
(* Qed. *)

(* Lemma denotation_application_lam Tx T ρ τ e : *)
(*   is_coverage_rty τ -> Tx ⤍ T = ⌊ ρ⇨τ ⌋ -> *)
(*   ∅ ⊢t vlam Tx e ⋮t Tx ⤍ T -> *)
(*   closed_rty ∅ (ρ⇨τ) -> *)
(*   (forall (v_x : value), *)
(*       ⟦ρ⟧ v_x -> *)
(*       ⟦τ ^r^ v_x⟧ (e ^t^ v_x)) -> *)
(*   (⟦ρ⇨τ⟧) (vlam Tx e). *)
(* Proof. *)
(*   intros Htm He Ht Hc H. *)
(*   split; [| split]; eauto. sinvert He; eauto. *)
(*   exists (vlam Tx e). split. pure_multistep_tac. intros v_x HDv_x. *)
(*   repeat rewrite_measure_irrelevant. *)
(*   specialize (H v_x HDv_x). *)
(*   eapply rtyR_refine; cycle 1; eauto. *)
(*   apply rtyR_typed_closed in HDv_x. simp_hyps. sinvert H0. *)
(*   split; intros. *)
(*   - apply rtyR_typed_closed in H. destruct H as [H _]. *)
(*     repeat esplit; eauto. *)
(*     rewrite <- rty_erase_open_eq. *)
(*     sinvert He. *)
(*     eapply mk_app_has_type; eauto. *)
(*   - apply reduction_mk_app'. *)
(*     rewrite reduction_tletapp_lam. *)
(*     intuition. basic_typing_regular_simp. basic_typing_regular_simp. *)
(*     rewrite reduction_nest_tlete; eauto. *)
(*   - rewrite is_coverage_rty_open; eauto. *)
(* Qed. *)

(* Lemma denotation_application_fixed (Tx : base_ty) T ϕ τ e : *)
(*   is_coverage_rty τ -> T = ⌊ τ ⌋ -> *)
(*   ∅ ⊢t vfix (Tx ⤍ T) (vlam (Tx ⤍ T) e) ⋮v Tx ⤍ T -> *)
(*   closed_rty ∅ ({:Tx|ϕ}⇨τ) -> *)
(*   (forall (v_x : value), *)
(*       ⟦{:Tx | ϕ}⟧ v_x -> *)
(*       ⟦({:Tx | (b0:v≺ v_x) & ϕ} ⇨ τ) ⇨ (τ ^r^ v_x)⟧ *)
(*         ((vlam (Tx ⤍ T) e) ^v^ v_x)) -> *)
(*   ⟦{:Tx | ϕ}⇨τ⟧ (vfix (Tx ⤍ T) (vlam (Tx ⤍ T) e)). *)
(* Proof. *)
(*   intros Htm He Ht Hc Hlam. *)
(*   split; [| split]; eauto. subst; eauto. *)
(*   exists (vfix (Tx ⤍ T) (vlam (Tx ⤍ T) e)). split. pure_multistep_tac. intros v_x HDc. *)
(*   repeat rewrite_measure_irrelevant. *)
(*   assert (exists c, v_x = vconst c) as H. { *)
(*     apply rtyR_typed_closed in HDc. *)
(*     destruct HDc as [H _]. sinvert H. *)
(*     eauto using basic_typing_base_canonical_form. *)
(*   } *)
(*   destruct H as [c ->]. *)
(*   induction c using (well_founded_induction constant_lt_well_founded). *)
(*   specialize (Hlam c HDc). *)
(*   destruct Hlam as (HTlam & HClam & (_ & _ & HDlam)). *)
(*   specialize (HDlam (vfix (Tx ⤍ T) (vlam (Tx ⤍ T) e))). subst. *)
(*   repeat rewrite_measure_irrelevant. *)
(*   rewrite open_rty_idemp in HDlam by eauto using lc. *)
(*   eapply rtyR_refine; cycle 1. *)
(*   2: { *)
(*     apply HDlam. *)
(*     split; [| split]; eauto. *)
(*     - sinvert HClam. econstructor. sinvert H0. eauto. my_set_solver. *)
(*     - exists (vfix (Tx ⤍ ⌊τ⌋) (vlam (Tx ⤍ ⌊τ⌋) e)). split. pure_multistep_tac. *)
(*       intros v_y HDv_y. *)
(*       repeat rewrite_measure_irrelevant. *)
(*       assert (exists y, v_y = vconst y). { *)
(*         apply rtyR_typed_closed in HDv_y. *)
(*         destruct HDv_y as [HTv_y _]. sinvert HTv_y. *)
(*         eauto using basic_typing_base_canonical_form. *)
(*       } *)
(*       destruct H0 as (y&->). *)
(*       destruct HDv_y as (HTy&_&Hy). *)
(*       assert (∀ α : list evop, α ⊧ y ↪*{ α} y) as Htmp by pure_multistep_tac. *)
(*       specialize (Hy y Htmp). *)
(*       rewrite qualifier_and_open in Hy. *)
(*       rewrite denote_qualifier_and in Hy. *)
(*       simp_hyps. *)
(*       apply H; eauto. *)
(*       apply denot_const_overrty; eauto. apply rtyR_typed_closed in HDc. simp_hyps; eauto. *)
(*   } *)
(*   split; intros. *)
(*   - subst. cbn in HTlam. *)
(*     repeat esplit. *)
(*     eapply mk_app_has_type; eauto. *)
(*     + apply rtyR_typed_closed in HDc. destruct HDc as [HTc _]. *)
(*       sinvert HTc. eauto. *)
(*     + eapply mk_app_has_type; eauto. simpl. *)
(*       rewrite <- rty_erase_open_eq in HTlam; eauto. *)
(*   - apply reduction_mk_app'. *)
(*     apply reduction_tletapp_fix. split; eauto. *)
(*     apply reduction_mk_app in H0; eauto. *)
(*     eauto using basic_typing_regular_value. *)
(*   - rewrite is_coverage_rty_open; eauto. *)
(* Qed. *)
