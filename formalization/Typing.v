From stdpp Require Import mapset.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import RefinementTypeProp.
From CT Require Import DenotationProp.
From CT Require Import InstantiationProp.

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


(** This file formalizes the type system of λᴱ and the main metatheoretic
  results. *)

(** Well-formedness (Fig. 5) *)

(* Definition wf_rty (Γ: listctx rty) (τ: rty): Prop := closed_rty (ctxdom Γ) τ. *)
(* | WfOver: forall Γ b ϕ, *)
(*     closed_rty (ctxdom Γ) {: b | ϕ } -> wf_rty Γ {: b | ϕ } *)
(* | WfUnder: forall Γ b ϕ a, *)
(*     closed_rty (ctxdom Γ) [: b | ϕ ]!<[ a ]> -> *)
(*     wf_td *)
(*     wf_rty Γ [: b | ϕ ]!<[ a ]> *)
(* | WfArr: forall Γ ρ τ (L: aset), *)
(*     wf_rty Γ ρ -> *)
(*     (forall x, x ∉ L -> wf_rty (Γ ++ [(x, ρ)]) (τ ^h^ x)) -> *)
(*     wf_rty Γ (ρ ⇨ τ) *)
(* | WfGhost: forall Γ b ρ (L: aset), *)
(*     (forall x, x ∉ L -> wf_rty (Γ ++ [(x, mk_top b)]) (ρ ^p^ x)) -> *)
(*     wf_rty Γ (b ⇢ ρ) *)

Notation " Γ '⊢WF' τ " := (closed_rty (ctxdom Γ) τ /\ is_coverage_rty τ) (at level 20, τ constr, Γ constr).

Reserved Notation "Γ '⊢' e '⋮' τ"  (at level 20).

(** Semantic subtyping *)
(* Instead of the syntactic subtyping relation presented in the paper, we use
semantic subtyping in the mechanization. *)
Definition subtyping (Γ: listctx rty) (ρ1 ρ2: rty) : Prop :=
  (* Assume [ρ1] and [ρ2] are valid [rty]s. *)
  ⌊ ρ1 ⌋ = ⌊ ρ2 ⌋ /\ (is_coverage_rty ρ1 <-> is_coverage_rty ρ2) /\
    forall epr, ctxRst Γ epr -> exists Γv, eprR epr Γv -> forall e, ⟦m{ Γv }r ρ1⟧ e → ⟦m{ Γv }r ρ2⟧ e.

Notation " Γ '⊢' τ1 '<⋮' τ2 " := (subtyping Γ τ1 τ2) (at level 20, τ1 constr, τ2 constr, Γ constr).

Definition join (Γ: listctx rty) (ρ1 ρ2 ρ3: rty) : Prop :=
  (* Assume [ρ1] and [ρ2] are valid [rty]s. *)
  ⌊ ρ1 ⌋ = ⌊ ρ2 ⌋ /\ ⌊ ρ1 ⌋ = ⌊ ρ3 ⌋ /\
    (is_coverage_rty ρ1 <-> is_coverage_rty ρ2) /\ (is_coverage_rty ρ1 <-> is_coverage_rty ρ3) /\
    forall epr, ctxRst Γ epr -> exists Γv, eprR epr Γv ->
                            forall e, ⟦m{ Γv }r ρ3⟧ e <-> ⟦m{ Γv }r ρ1⟧ e \/ ⟦m{ Γv }r ρ2⟧ e.

Notation " Γ '⊢' τ1 '<⋮' τ2 " := (subtyping Γ τ1 τ2) (at level 20, τ1 constr, τ2 constr, Γ constr).

Notation " Γ '⊢' τ1 '⋮merge' τ2 '⋮=' τ3" := (join Γ τ1 τ2 τ3) (at level 20, τ1 constr, τ2 constr, τ3 constr, Γ constr).

(* The builtin typing relation (Δ) that our type system is parameterized over. *)
Parameter builtin_typing_relation : effop -> rty -> Prop.

Reserved Notation "Γ '⊢' op '⋮o' ρ"  (at level 20).
Reserved Notation "Γ '⊢' e '⋮t' τ" (at level 20).
Reserved Notation "Γ '⊢' e '⋮v' τ" (at level 20).

(** * Typing rules (Fig. 6) *)

Inductive effop_type_check : listctx rty -> effop -> rty -> Prop :=
| TEOp : forall Γ op ρ_op ρ,
    Γ ⊢WF ρ ->
    builtin_typing_relation op ρ_op ->
    (* [TSubEOp] is inlined here. Consecutive applications of subtyping is just
    one subtyping. *)
    Γ ⊢ ρ_op <⋮ ρ ->
    ⌊ ρ ⌋ = ty_of_op op ->
    Γ ⊢ op ⋮o ρ
where
"Γ '⊢' op '⋮o' ρ" := (effop_type_check Γ op ρ).

(** Typing rules for values and terms. Values always have refinement types, while
  terms always have Hoare automata types. *)
Inductive term_type_check : listctx rty -> tm -> rty -> Prop :=
| TErr: forall Γ (b: base_ty), Γ ⊢WF (mk_bot b) -> Γ ⊢ (terr b) ⋮t (mk_bot b)
| TValue: forall Γ v τ, Γ ⊢ v ⋮v τ -> Γ ⊢ (treturn v) ⋮t τ
| TSub: forall Γ e (τ1 τ2: rty),
    Γ ⊢WF τ2 ->
    Γ ⊢ e ⋮t τ1 ->
    Γ ⊢ τ1 <⋮ τ2 ->
    Γ ⊢ e ⋮t τ2
| TMerge: forall Γ e (τ1 τ2 τ3: rty),
    Γ ⊢WF τ3 ->
    Γ ⊢ e ⋮t τ1 ->
    Γ ⊢ e ⋮t τ2 ->
    Γ ⊢ τ1 ⋮merge τ2 ⋮= τ3 ->
    Γ ⊢ e ⋮t τ3
| TLetE: forall Γ e1 e2 τ1 τ2 (L: aset),
    (forall x, x ∉ L -> (Γ ++ [(x, τ1)]) ⊢ (e2 ^t^ x) ⋮t τ2) ->
    Γ ⊢WF τ2 ->
    Γ ⊢ e1 ⋮t τ1 ->
    Γ ⊢ (tlete e1 e2) ⋮t τ2
| TAppOverParam: forall Γ (v1 v2: value) e b ϕ τ1 τ2 (L: aset),
    (forall x, x ∉ L -> (Γ ++ [(x, τ1 ^r^ v2)]) ⊢ (e ^t^ x) ⋮t τ2) ->
    Γ ⊢WF τ2 ->
    Γ ⊢ v2 ⋮v [:b | ϕ] ->
    Γ ⊢ v1 ⋮v ({:b | ϕ} ⇨ τ1) ->
    Γ ⊢ (tletapp v1 v2 e) ⋮t τ2
| TAppFuncParam: forall Γ (v1 v2: value) e ρ1 ρ2 τ1 τ2 (L: aset),
    (forall x, x ∉ L -> (Γ ++ [(x, τ1 ^r^ v2)]) ⊢ (e ^t^ x) ⋮t τ2) ->
    Γ ⊢WF τ2 ->
    Γ ⊢ v2 ⋮v (ρ1 ⇨ ρ2) ->
    Γ ⊢ v1 ⋮v ((ρ1 ⇨ ρ2) ⇨ τ1) ->
    Γ ⊢ (tletapp v1 v2 e) ⋮t τ2
| TAppOp: forall Γ (op: effop) (v2: value) e b ϕ b1 ϕ1 τ2 (L: aset),
    (forall x, x ∉ L -> (Γ ++ [(x, [: b1 | ϕ1] ^r^ v2)]) ⊢ (e ^t^ x) ⋮t τ2) ->
    Γ ⊢WF τ2 ->
    Γ ⊢ v2 ⋮v [: b | ϕ] ->
    Γ ⊢ op ⋮o ({: b | ϕ} ⇨ [: b1 | ϕ1]) ->
    Γ ⊢ (tleteffop op v2 e) ⋮t τ2
| TMatchbTrue: forall Γ (v: value) e1 e2 ϕ τ (L : aset),
    Γ ⊢WF τ ->
    Γ ⊢ v ⋮v [:TBool | ϕ] ->
    (forall x, x ∉ L -> (Γ ++ [(x, [: TBool | b0:c=true & b0:v= v & ϕ])]) ⊢ e1 ⋮t τ) ->
    Γ ⊢ (tmatchb v e1 e2) ⋮t τ
| TMatchbFalse: forall Γ (v: value) e1 e2 ϕ τ (L : aset),
    Γ ⊢WF τ ->
    Γ ⊢ v ⋮v [:TBool | ϕ] ->
    (forall x, x ∉ L -> (Γ ++ [(x, [: TBool | b0:c=false & b0:v= v & ϕ])]) ⊢ e2 ⋮t τ) ->
    Γ ⊢ (tmatchb v e1 e2) ⋮t τ
with value_type_check : listctx rty -> value -> rty -> Prop :=
| TSubPP: forall Γ (v: value) (ρ1 ρ2: rty),
    Γ ⊢WF ρ2 ->
    Γ ⊢ v ⋮v ρ1 ->
    Γ ⊢ ρ1 <⋮ ρ2 ->
    Γ ⊢ v ⋮v ρ2
| TConst: forall Γ (c: constant),
    Γ ⊢WF (mk_eq_constant c) ->
    Γ ⊢ c ⋮v (mk_eq_constant c)
| TBaseVar: forall Γ (x: atom) b ϕ,
    Γ ⊢WF (mk_eq_var b x) ->
    ctxfind Γ x = Some {: b | ϕ} ->
    Γ ⊢ x ⋮v (mk_eq_var b x)
| TFuncVar: forall Γ (x: atom) ρ τ,
    Γ ⊢WF (ρ ⇨ τ) ->
    ctxfind Γ x = Some (ρ ⇨ τ) ->
    Γ ⊢ x ⋮v (ρ ⇨ τ)
| TFun: forall Γ Tx ρ e τ (L: aset),
    Γ ⊢WF (ρ ⇨ τ) ->
    (forall x, x ∉ L -> (Γ ++ [(x, ρ)]) ⊢ (e ^t^ x) ⋮t (τ ^r^ x)) ->
    Tx = ⌊ ρ ⌋ ->
    Γ ⊢ (vlam Tx e) ⋮v (ρ ⇨ τ)
| TFix: forall Γ (Tx : base_ty) ϕ e τ T (L: aset),
    Γ ⊢WF ({: Tx | ϕ} ⇨ τ) ->
    (* NOTE: should not open the whole type, because the first argument (bound *)
(*     variable 0) of the return type is not the fixed point function but [{: Tx | *)
(*     ϕ}]. The return type should be opened by [x]. *)
    (forall x, x ∉ L ->
          (Γ ++ [(x, {: Tx | ϕ})]) ⊢ (vlam (Tx ⤍ T) e) ^v^ x ⋮v (({: Tx | b0:x≺ x & ϕ} ⇨ τ) ⇨ (τ ^r^ x))) ->
    T = ⌊ τ ⌋ ->
    Γ ⊢ (vfix (Tx ⤍ T) (vlam (Tx ⤍ T) e)) ⋮v ({: Tx | ϕ} ⇨ τ)
where
"Γ '⊢' e '⋮t' τ" := (term_type_check Γ e τ) and "Γ '⊢' e '⋮v' ρ" := (value_type_check Γ e ρ).

Scheme value_term_type_check_ind := Minimality for value_type_check Sort Prop
    with term_value_type_check_ind := Minimality for term_type_check Sort Prop.
Combined Scheme value_term_type_check_mutind from
  value_term_type_check_ind, term_value_type_check_ind.

(** * Properties of the type system *)

Lemma subtyping_preserves_basic_typing Γ τ1 τ2 :
  Γ ⊢ τ1 <⋮ τ2 ->
  ⌊τ1⌋ = ⌊τ2⌋.
Proof.
  qauto.
Qed.

Lemma rty_subtyping_preserves_basic_typing Γ ρ1 ρ2 :
  Γ ⊢ ρ1 <⋮ ρ2 ->
  ⌊ρ1⌋ = ⌊ρ2⌋.
Proof.
  qauto.
Qed.

Lemma subtyping_preserves_is_coverage_rty Γ τ1 τ2 :
  Γ ⊢ τ1 <⋮ τ2 -> is_coverage_rty τ1 <-> is_coverage_rty τ2.
Proof.
  qauto.
Qed.


Lemma effop_typing_preserves_basic_typing Γ ρ op :
  Γ ⊢ op ⋮o ρ ->
  ⌊ρ⌋ = ty_of_op op.
Proof.
  inversion 1; subst. eauto.
Qed.

Lemma value_typing_regular_wf : forall (Γ: listctx rty) (v: value) (ρ: rty),
    Γ ⊢ v ⋮v ρ -> Γ ⊢WF ρ
with tm_typing_regular_wf : forall (Γ: listctx rty) (e: tm) (τ: rty),
    Γ ⊢ e ⋮t τ -> Γ ⊢WF τ.
Proof.
  all: destruct 1; eauto.
Qed.

Lemma value_tm_typing_regular_is_coverage_rty:
  (forall (Γ: listctx rty) (v: value) (ρ: rty),
      Γ ⊢ v ⋮v ρ -> is_coverage_rty ρ) /\
    (forall (Γ: listctx rty) (e: tm) (τ: rty),
        Γ ⊢ e ⋮t τ -> is_coverage_rty τ).
Proof.
  split; intros.
  - apply value_typing_regular_wf in H; intuition.
  - apply tm_typing_regular_wf in H; intuition.
Qed.

Lemma value_tm_typing_regular_basic_typing:
  (forall (Γ: listctx rty) (v: value) (ρ: rty),
    Γ ⊢ v ⋮v ρ -> ⌊ Γ ⌋* ⊢t v ⋮v ⌊ ρ ⌋) /\
  (forall (Γ: listctx rty) (e: tm) (τ: rty),
    Γ ⊢ e ⋮t τ -> ⌊ Γ ⌋* ⊢t e ⋮t ⌊ τ ⌋).
Proof.
  apply value_term_type_check_mutind; intros; cbn; subst; eauto.
  - hauto using rty_subtyping_preserves_basic_typing.
  - (* TBaseVar *) econstructor. qauto using ctx_erase_lookup.
  - (* TFuncVar *) econstructor. qauto using ctx_erase_lookup.
  - (* TFun *) econstructor.
    instantiate_atom_listctx.
    rewrite ctx_erase_app_r in H1 by my_set_solver.
    rewrite <- rty_erase_open_eq in H1.
    eauto.
  - (* TFix *) econstructor.
    instantiate_atom_listctx.
    rewrite ctx_erase_app_r in H1 by my_set_solver.
    cbn in H1.
    rewrite <- rty_erase_open_eq in H1.
    eauto.
  - hauto using subtyping_preserves_basic_typing.
  - hauto using subtyping_preserves_basic_typing.
(*   - destruct ρ1; simpl in *. *)
(*     all: econstructor; eauto; *)
(*       instantiate_atom_listctx; *)
(*       rewrite ctx_erase_app_r in H0 by my_set_solver; eauto. *)
(*   - destruct ρ1; simpl in *. *)
(*     all: auto_exists_L; intros; repeat specialize_with x; *)
(*         rewrite ctx_erase_app_r in H0 by my_set_solver; *)
(*         simpl in H0; repeat rewrite <- rty_erase_open_eq in H0; eauto. *)
(*   - apply effop_typing_preserves_basic_typing in H4. cbn in H4. sinvert H4. *)
(*     econstructor; eauto. qauto. *)
(*     instantiate_atom_listctx. *)
(*     rewrite ctx_erase_app_r in H0 by my_set_solver. *)
(*     rewrite <- rty_erase_open_eq in H0; eauto. *)
(*   - auto_pose_fv x. repeat specialize_with x. *)
(*     rewrite ctx_erase_app_r in H3, H5 by my_set_solver. *)
(*     econstructor; eauto. *)
(*     eapply basic_typing_strengthen_tm; eauto. my_set_solver. *)
(*     eapply basic_typing_strengthen_tm; eauto. my_set_solver. *)
(* Qed. *)
Admitted.

Lemma value_typing_regular_basic_typing: forall (Γ: listctx rty) (v: value) (ρ: rty),
    Γ ⊢ v ⋮v ρ -> ⌊ Γ ⌋* ⊢t v ⋮v ⌊ ρ ⌋.
Proof.
  apply value_tm_typing_regular_basic_typing.
Qed.

Lemma tm_typing_regular_basic_typing: forall (Γ: listctx rty) (e: tm) (τ: rty),
    Γ ⊢ e ⋮t τ -> ⌊ Γ ⌋* ⊢t e ⋮t ⌊ τ ⌋.
Proof.
  apply value_tm_typing_regular_basic_typing.
Qed.

(* Lemma ctxRst_insert_easy Γ P (x: atom) ρ P': *)
(*     ctxRst Γ P -> *)
(*     x ∉ ctxdom Γ -> *)
(*     (forall env (v: value), ⟦ m{ env }r ρ ⟧ v -> P env <-> P' (<[ x := v ]> env)) -> *)
(*     ctxRst (Γ ++ [(x, ρ)]) P'. *)
(* Proof. *)
(*   intros. econstructor; eauto. *)
(*   econstructor; eauto using ctxRst_ok_ctx. *)
(*   apply rtyR_typed_closed in H1. simp_hyps. *)
(*   (* This should be a lemma similar to [msubst_preserves_closed_rty_empty], or *)
(*   we should strenghthen this lemma. But don't bother now as it is only used *)
(*   here. *) *)
(*   sinvert H3. *)
(*   econstructor. eauto using lc_msubst_rty, ctxRst_lc. *)
(*   rewrite fv_of_msubst_rty_closed in H5 by eauto using ctxRst_closed_env. *)
(*   rewrite ctxRst_dom in * by eauto. *)
(*   my_set_solver. *)
(* Qed. *)

(* Lemma ctxRst_ctxfind Γ Γv x ρ : *)
(*   ctxRst Γ Γv -> *)
(*   ctxfind Γ x = Some ρ -> *)
(*   fine_rty ρ -> *)
(*   exists (v : value), Γv !! x = Some v /\ ⟦ m{ Γv }r ρ ⟧ v. *)
(* Proof. *)
(*   induction 1. *)
(*   - easy. *)
(*   - intros. *)
(*     select (ctxfind (_ ++ _) _ = _) *)
(*       (fun H => apply ctxfind_app in H; eauto using ok_ctx_ok). *)

(*     assert (forall (v' : value), (⟦(m{env}r) ρ⟧) v' -> *)
(*                             (⟦(m{<[x0:=v]> env}r) ρ⟧) v'). { *)
(*       select (⟦ _ ⟧ _) (fun H => apply rtyR_typed_closed in H). simp_hyps. *)
(*       intros. *)
(*       apply rtyR_msubst_insert_eq; eauto using ctxRst_closed_env. *)
(*       select (_ ⊢t _ ⋮t _) *)
(*         (fun H => apply basic_typing_contains_fv_tm in H; simpl in H). *)
(*       my_set_solver. *)
(*       select (ok_ctx _) (fun H => apply ok_ctx_ok in H; apply ok_post_destruct in H). *)
(*       srewrite ctxRst_dom. *)
(*       simp_hyps. *)
(*       apply not_elem_of_dom. eauto. *)
(*     } *)
(*     destruct_or!; simp_hyps. *)
(*     + eexists. split; eauto. *)
(*       assert (x <> x0). { *)
(*         select (ok_ctx _) (fun H => sinvert H); listctx_set_simpl. *)
(*         select (ctxfind _ _ = _) (fun H => apply ctxfind_some_implies_in_dom in H). *)
(*         my_set_solver. *)
(*       } *)
(*       by simplify_map_eq. *)
(*     + simpl in *. *)
(*       case_decide; try easy. simplify_eq. *)
(*       eexists. split; eauto. by simplify_map_eq. *)
(* Qed. *)

Ltac msubst_erase_simp :=
  repeat match goal with
    | [H: context [ ⌊ ?τ ⌋ ] |- _ ] =>
        match τ with
        | context [ m{_}r _ ] => setoid_rewrite <- rty_erase_msubst_eq in H
        end
    | [H: _ |- context [ ⌊ ?τ ⌋ ]] =>
        match τ with
        | context [ m{_}r _ ] => setoid_rewrite <- rty_erase_msubst_eq
        end
    end.
