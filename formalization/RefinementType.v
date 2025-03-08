Require Import Coq.Program.Wf.
From stdpp Require Import mapset.
From stdpp Require Import natmap.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import Qualifier.
From CT Require Import ListCtx.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import OperationalSemantics.
Import BasicTyping.
Import Qualifier.
Import ListCtx.
Import List.

(** Refinement types (t in Fig. 4) *)
Inductive rty : Type :=
| rtyOver (b: base_ty) (ϕ: qualifier)
| rtyUnder (b: base_ty) (ϕ: qualifier)
| rtyArr (ρ: rty) (τ: rty).

Global Hint Constructors rty: core.

Notation "'{:' b '|' ϕ '}'" := (rtyOver b ϕ) (at level 5, format "{: b | ϕ }", b constr, ϕ constr).
Notation "'[:' b '|' ϕ ']' " := (rtyUnder b ϕ) (at level 5, format "[: b | ϕ ]", b constr, ϕ constr).
Notation "ρ '⇨' τ" :=
  (rtyArr ρ τ) (at level 80, format "ρ ⇨ τ", right associativity, ρ constr, τ constr).

(* NOTE: \rightwhitearrow: ⇨ *)

Definition is_under_base_rty (τ: rty) :=
  match τ with
  | [: _ | _ ] => False
  | _ => True
  end.

Definition is_over_base_rty (τ: rty) :=
  match τ with
  | {: _ | _ } => False
  | _ => True
  end.

(* This measure function is used to guarantee termination of the denotation.
Instead of addtion, we can also use [max] for the subterms. *)
Fixpoint rty_measure (ρ: rty) : nat :=
  match ρ with
  | rtyOver _ _ | rtyUnder _ _ => 1
  | ρ ⇨ τ => 1 + rty_measure ρ + rty_measure τ
  end.

Inductive is_coverage_rty: rty -> Prop :=
| is_coverage_rty_base: forall b ϕ, is_coverage_rty [:b|ϕ]
| is_coverage_rty_over_arr: forall b ϕ τ,
    is_coverage_rty τ -> is_coverage_rty ({:b|ϕ} ⇨ τ)
| is_coverage_rty_under_arr: forall b ϕ τ,
    is_coverage_rty τ -> is_coverage_rty ([:b|ϕ] ⇨ τ)
| is_coverage_rty_arr_arr: forall ρ1 ρ2 τ,
    is_coverage_rty (ρ1 ⇨ ρ2) -> is_coverage_rty τ -> is_coverage_rty ((ρ1 ⇨ ρ2) ⇨ τ).

Global Hint Constructors is_coverage_rty: core.

Definition fine_rty (τ: rty) :=
  match τ with
  | {: _ | _ } => True
  | [: _ | _ ] => True
  | _ => is_coverage_rty τ
  end.

Definition flip_rty (τ: rty) :=
  match τ with
  | [: b | ϕ ] => {: b | ϕ }
  | {: b | ϕ } => [: b | ϕ ]
  | ρ ⇨ τ => ρ ⇨ τ
  end.

(** Type erasure (Fig. 5) *)

Fixpoint rty_erase ρ : ty :=
  match ρ with
  | {: b | ϕ } => b
  | [: b | ϕ ] => b
  | ρ ⇨ τ => (rty_erase ρ) ⤍ (rty_erase τ)
  end.

Notation " '⌊' ty '⌋' " := (rty_erase ty) (at level 5, format "⌊ ty ⌋", ty constr).

Definition ctx_erase (Γ: listctx rty) :=
  ⋃ ((List.map (fun e => {[e.1 := rty_erase e.2]}) Γ): list (amap ty)).

Notation " '⌊' Γ '⌋*' " := (ctx_erase Γ) (at level 5, format "⌊ Γ ⌋*", Γ constr).

(** * Naming related definitions *)

Fixpoint rty_fv ρ : aset :=
  match ρ with
  | {: _ | ϕ } => qualifier_fv ϕ
  | [: _ | ϕ ] => qualifier_fv ϕ
  | ρ ⇨ τ => rty_fv ρ ∪ rty_fv τ
  end.

#[global]
  Instance rty_stale : @Stale aset rty := rty_fv.
Arguments rty_stale /.

Fixpoint rty_open (k: nat) (s: value) (ρ: rty) : rty :=
  match ρ with
  | {: b | ϕ } => {: b | qualifier_open (S k) s ϕ }
  | [: b | ϕ ] => [: b | qualifier_open (S k) s ϕ ]
  | ρ ⇨ τ => (rty_open k s ρ) ⇨ (rty_open (S k) s τ)
  end.

Notation "'{' k '~r>' s '}' e" := (rty_open k s e) (at level 20, k constr).
Notation "e '^r^' s" := (rty_open 0 s e) (at level 20).

Fixpoint rty_subst (k: atom) (s: value) (ρ: rty) : rty :=
  match ρ with
  | {: b | ϕ} => {: b | qualifier_subst k s ϕ}
  | [: b | ϕ] => [: b | qualifier_subst k s ϕ]
  | ρ ⇨ τ => (rty_subst k s ρ) ⇨ (rty_subst k s τ)
  end.

Notation "'{' x ':=' s '}r'" := (rty_subst x s) (at level 20, format "{ x := s }r", x constr).

(** Local closure *)
(** NOTE: To alaign with denotation, we assume the function type doesn't appear in transduce. *)
(** NOTE: all (L: aset) should be the first hypothesis. *)
Inductive lc_rty : rty -> Prop :=
| lc_rtyOver: forall b ϕ, lc_phi1 ϕ -> fine_rty {: b | ϕ} -> lc_rty {: b | ϕ}
| lc_rtyUnder: forall b ϕ, lc_phi1 ϕ -> fine_rty [: b | ϕ] -> lc_rty [: b | ϕ]
| lc_rtyArr: forall ρ τ (L : aset),
    (forall x : atom, x ∉ L -> lc_rty (τ ^r^ x)) ->
    fine_rty (ρ ⇨ τ) -> lc_rty ρ ->
    lc_rty (ρ ⇨ τ).

Lemma lc_rty_fine: forall τ, lc_rty τ -> fine_rty τ.
Proof.
  induction 1; eauto.
Qed.

Definition body_rty τ := exists (L: aset), ∀ x : atom, x ∉ L → lc_rty (τ ^r^ x).

(** Closed under free variable set *)

Inductive closed_rty (d : aset) (ρ: rty): Prop :=
| closed_rty_: lc_rty ρ -> rty_fv ρ ⊆ d -> closed_rty d ρ.

Lemma closed_rty_fine: forall d τ, closed_rty d τ -> fine_rty τ.
Proof.
  pose lc_rty_fine.
  induction 1; eauto.
Qed.

(** Well-formedness of type context. All terms and types are alpha-converted to
  have unique names.
  all rty in ctx are pure.
 *)
Inductive ok_ctx: listctx rty -> Prop :=
| ok_ctx_nil: ok_ctx []
| ok_ctx_cons: forall (Γ: listctx rty)(x: atom) (ρ: rty),
    ok_ctx Γ ->
    closed_rty (ctxdom Γ) ρ ->
    x ∉ ctxdom Γ ->
    ok_ctx (Γ ++ [(x, ρ)]).

Lemma ok_ctx_ok: forall Γ, ok_ctx Γ -> ok Γ.
Proof.
  induction 1; eauto.
Qed.

Lemma is_over_base_rty_open: forall τ k (v_x: value), is_over_base_rty ({ k ~r> v_x} τ) <-> is_over_base_rty τ.
Proof.
  split; induction τ; simpl; intros; inversion H; subst; eauto.
Qed.

Lemma is_over_base_rty_subst: forall τ x (v_x: value), is_over_base_rty ({ x := v_x}r τ) <-> is_over_base_rty τ.
Proof.
  split; induction τ; simpl; intros; inversion H; subst; eauto.
Qed.

Lemma is_under_base_rty_open: forall τ k (v_x: value), is_under_base_rty ({ k ~r> v_x} τ) <-> is_under_base_rty τ.
Proof.
  split; induction τ; simpl; intros; inversion H; subst; eauto.
Qed.

Lemma is_under_base_rty_subst: forall τ x (v_x: value), is_under_base_rty ({ x := v_x}r τ) <-> is_under_base_rty τ.
Proof.
  split; induction τ; simpl; intros; inversion H; subst; eauto.
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

Lemma is_coverage_rty_open_aux n: forall τ, rty_measure τ <= n -> forall k (v_x: value), is_coverage_rty ({ k ~r> v_x} τ) <-> is_coverage_rty τ.
Proof.
  induction n; split; intros HH.
  - destruct τ; sinvert H.
  - destruct τ; sinvert H.
  - destruct τ.
    + sinvert HH; eauto.
    + sinvert HH; eauto.
    + destruct τ1; sinvert HH; eauto; econstructor; rewrite <- IHn; eauto; simpl in *; lia.
  - destruct τ.
    + sinvert HH; eauto.
    + simpl. eauto.
    + destruct τ1; sinvert HH; eauto; simpl; econstructor; try solve [rewrite IHn; eauto; simpl in *; lia].
      * rewrite <- IHn in H2; eauto; simpl in *; lia.
Qed.

Lemma is_coverage_rty_open: forall τ, forall k (v_x: value), is_coverage_rty ({ k ~r> v_x} τ) <-> is_coverage_rty τ.
Proof. eauto using is_coverage_rty_open_aux. Qed.

Lemma is_coverage_rty_subst_aux n: forall τ, rty_measure τ <= n -> forall x (v_x: value), is_coverage_rty ({ x := v_x}r τ) <-> is_coverage_rty τ.
Proof.
  induction n; split; intros HH.
  - destruct τ; sinvert H.
  - destruct τ; sinvert H.
  - destruct τ.
    + sinvert HH; eauto.
    + sinvert HH; eauto.
    + destruct τ1; sinvert HH; eauto; econstructor; rewrite <- IHn; eauto; simpl in *; lia.
  - destruct τ.
    + sinvert HH; eauto.
    + simpl. eauto.
    + destruct τ1; sinvert HH; eauto; simpl; econstructor; try solve [rewrite IHn; eauto; simpl in *; lia].
      * rewrite <- IHn in H2; eauto; simpl in *; lia.
Qed.

Lemma is_coverage_rty_subst: forall τ x (v_x: value), is_coverage_rty ({ x := v_x}r τ) <-> is_coverage_rty τ.
Proof. eauto using is_coverage_rty_subst_aux. Qed.

Lemma rty_open_arr_rev: forall ρ τ k v, (({k ~r> v} ρ) ⇨ ({S k ~r> v} τ)) = {k ~r> v} (ρ ⇨ τ).
Proof. eauto. Qed.

Lemma rty_subst_arr_rev: forall ρ τ x v, (({x := v}r ρ) ⇨ ({x := v}r τ)) = {x := v}r (ρ ⇨ τ).
Proof. eauto. Qed.

Ltac fine_rty_aux_simp_aux :=
  match goal with
  | [H: context [ (({?k ~r> ?v} _) ⇨ ({S ?k ~r> ?v} _)) ] |- _ ] =>
      setoid_rewrite rty_open_arr_rev in H
  | [H: context [ (({?x := ?v}r _) ⇨ ({?x := ?v}r _)) ] |- _ ] =>
      setoid_rewrite rty_subst_arr_rev in H
  | [H: _ |- context [ (({?k ~r> ?v} _) ⇨ ({S ?k ~r> ?v} _)) ]] =>
      setoid_rewrite rty_open_arr_rev
  | [H: _ |- context [ (({?x := ?v}r _) ⇨ ({?x := ?v}r _)) ] ] =>
      setoid_rewrite rty_subst_arr_rev
  | [H: context [ is_over_base_rty ({_ ~r> _} ?τ) ] |- _ ] => setoid_rewrite is_over_base_rty_open in H
  | [H: context [ is_over_base_rty ({_ := _}r ?τ) ] |- _ ] => setoid_rewrite is_over_base_rty_subst in H
  | [H: _ |- context [ is_over_base_rty ({_ ~r> _} ?τ) ] ] => setoid_rewrite is_over_base_rty_open
  | [H: _ |- context [ is_over_base_rty ({_ := _}r ?τ) ] ] => setoid_rewrite is_over_base_rty_subst
  | [H: context [ is_under_base_rty ({_ ~r> _} ?τ) ] |- _ ] => setoid_rewrite is_under_base_rty_open in H
  | [H: context [ is_under_base_rty ({_ := _}r ?τ) ] |- _ ] => setoid_rewrite is_under_base_rty_subst in H
  | [H: _ |- context [ is_under_base_rty ({_ ~r> _} ?τ) ] ] => setoid_rewrite is_under_base_rty_open
  | [H: _ |- context [ is_under_base_rty ({_ := _}r ?τ) ] ] => setoid_rewrite is_under_base_rty_subst
  | [H: context [ is_coverage_rty ({_ ~r> _} ?τ) ] |- _ ] => setoid_rewrite is_coverage_rty_open in H
  | [H: context [ is_coverage_rty ({_ := _}r ?τ) ] |- _ ] => setoid_rewrite is_coverage_rty_subst in H
  | [H: _ |- context [ is_coverage_rty ({_ ~r> _} ?τ) ] ] => setoid_rewrite is_coverage_rty_open
  | [H: _ |- context [ is_coverage_rty ({_ := _}r ?τ) ] ] => setoid_rewrite is_coverage_rty_subst
  end.

Lemma fine_rty_open τ: forall k (v_x: value), fine_rty ({ k ~r> v_x} τ) <-> fine_rty τ.
Proof.
  split; intros; destruct τ; simpl in *; repeat fine_rty_aux_simp_aux; eauto.
Qed.

Lemma fine_rty_subst: forall τ x (v_x: value), fine_rty ({ x := v_x}r τ) <-> fine_rty τ.
Proof.
  split; intros; destruct τ; simpl in *; repeat fine_rty_aux_simp_aux; eauto.
Qed.

Ltac fine_rty_simp_aux :=
  match goal with
  | [H: context [ (({?k ~r> ?v} _) ⇨ ({S ?k ~r> ?v} _)) ] |- _ ] =>
      setoid_rewrite rty_open_arr_rev in H
  | [H: context [ (({?x := ?v}r _) ⇨ ({?x := ?v}r _)) ] |- _ ] =>
      setoid_rewrite rty_subst_arr_rev in H
  | [H: _ |- context [ (({?k ~r> ?v} _) ⇨ ({S ?k ~r> ?v} _)) ]] =>
      setoid_rewrite rty_open_arr_rev
  | [H: _ |- context [ (({?x := ?v}r _) ⇨ ({?x := ?v}r _)) ] ] =>
      setoid_rewrite rty_subst_arr_rev
  | [H: context [ fine_rty ({_ ~r> _} ?τ) ] |- _ ] => setoid_rewrite fine_rty_open in H
  | [H: context [ fine_rty ({_ := _}r ?τ) ] |- _ ] => setoid_rewrite fine_rty_subst in H
  | [H: _ |- context [ fine_rty ({_ ~r> _} ?τ) ] ] => setoid_rewrite fine_rty_open
  | [H: _ |- context [ fine_rty ({_ := _}r ?τ) ] ] => setoid_rewrite fine_rty_subst
  | _ => fine_rty_aux_simp_aux
  end.

(** Shorthands, used in typing rules *)
Definition mk_eq_constant c := [: ty_of_const c | b0:c= c ].
Definition mk_eq_constant_over c := {: ty_of_const c | b0:c= c }.
Definition mk_bot ty := [: ty | mk_q_under_bot ].
Definition mk_top ty := [: ty | mk_q_under_top ].
Definition mk_eq_var ty (x: atom) := [: ty | b0:x= x ].

Lemma lc_rty_under_base_q: forall b ϕ, lc_rty ([:b|ϕ]) <-> lc_phi1 ϕ.
Proof.
  split; intros; sinvert H; eauto.
  econstructor; eauto. exists x. eauto. simpl; eauto.
Qed.

Lemma lc_rty_over_base_q: forall b ϕ, lc_rty ({:b|ϕ}) <-> lc_phi1 ϕ.
Proof.
  split; intros; sinvert H; eauto.
  econstructor; eauto. exists x. eauto. simpl; eauto.
Qed.

Lemma lc_rty_base_flip: forall b ϕ, lc_rty {:b|ϕ} <-> lc_rty [:b|ϕ].
Proof.
  split; intros; sinvert H; econstructor; eauto.
Qed.

Lemma closed_rty_base_flip: forall L b ϕ, closed_rty L {:b|ϕ} <-> closed_rty L [:b|ϕ].
Proof.
  split; intros; sinvert H; econstructor; eauto;
  rewrite lc_rty_base_flip in *; eauto.
Qed.

Lemma lc_rty_arr: forall ρ τ, lc_rty (ρ ⇨ τ) <-> fine_rty (ρ ⇨ τ) /\ lc_rty ρ /\ body_rty τ.
Proof.
  split; intros; sinvert H.
  - intuition. auto_exists_L.
  - unfold body_rty in H1. simp_hyps. auto_exists_L; eauto.
Qed.

Lemma closed_rty_arr:
  ∀ (L : aset) (ρ τ : rty),
    closed_rty L (ρ⇨τ) ↔ (fine_rty (ρ⇨τ)) /\ closed_rty L ρ ∧ body_rty τ /\ (rty_fv τ ⊆ L).
Proof.
  split; intros.
  - sinvert H. rewrite lc_rty_arr in H0. intuition.
    + econstructor; eauto. my_set_solver.
    + my_set_solver.
  - simp_hyps. sinvert H1. econstructor; eauto.
    + rewrite lc_rty_arr. intuition.
    + my_set_solver.
Qed.

Ltac fine_rty_simp := simpl in *; repeat fine_rty_simp_aux.

Ltac fine_rty_solver := fine_rty_simp; eauto.
