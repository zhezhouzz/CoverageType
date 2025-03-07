From stdpp Require Import mapset.
From stdpp Require Import natmap.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import Qualifier.
From CT Require Import ListCtx.
From CT Require Import Transducer.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import OperationalSemantics.
Import BasicTyping.
Import Qualifier.
Import ListCtx.
Import List.
Import Transducer.

(** * Naming properties of refinement type syntax *)

(** * subst *)

Ltac my_simplify_map :=
  (repeat match goal with
     | [H: context [ _ ∪ ∅ ] |- _ ] => setoid_rewrite map_union_empty in H
     | [H: _ |- context [ _ ∪ ∅ ] ] => setoid_rewrite map_union_empty
     | [H: context [ insert _ _ ∅ ] |- _ ] => setoid_rewrite insert_empty in H
     | [H: _ |- context [ insert _ _ ∅  ] ] => setoid_rewrite insert_empty
     end).

Lemma subst_commute_td : forall x u_x y u_y a,
    x <> y -> x ∉ fv_value u_y -> y ∉ fv_value u_x ->
    {x := u_x }a ({y := u_y }a a) = {y := u_y }a ({x := u_x }a a).
Proof.
  pose subst_commute_value.
  pose subst_commute_qualifier.
  intros.
  induction a; simpl; eauto; f_equal; eauto.
Qed.

Lemma subst_fresh_td: forall (a: transducer) (x:atom) (u: value),
    x # a -> {x := u}a a = a.
Proof.
  pose subst_fresh_qualifier.
  pose subst_fresh_value.
  intros.
  induction a; simpl in *; eauto; repeat f_equal;
  try (auto_apply; my_set_solver).
Qed.

Lemma open_fv_td (a : transducer) (v : value): forall k,
  td_fv ({k ~a> v} a) ⊆ td_fv a ∪ fv_value v.
Proof.
  pose open_fv_qualifier.
  pose open_fv_value.
  induction a; simpl; intros; eauto; my_set_solver.
Qed.

Lemma open_fv_td' (a : transducer) (v : value): forall k,
  td_fv a ⊆ td_fv ({k ~a> v} a).
Proof.
  pose open_fv_qualifier'.
  pose open_fv_value'.
  induction a; intros; simpl; eauto; my_set_solver.
Qed.

Lemma open_subst_same_td: forall x y (a : transducer) k,
    x # a ->
    {x := y }a ({k ~a> x} a) = {k ~a> y} a.
Proof.
  induction a; cbn; intros; eauto.
  f_equal. eauto using open_subst_same_qualifier.
  all:
  repeat
    match goal with
    | H : forall k, _ # _ -> _ =_ |- _ => rewrite H by my_set_solver; eauto
    | H : forall k, _ ∉ _ -> _ =_ |- _ => rewrite H by my_set_solver; eauto
    end.
  - rewrite open_subst_same_qualifier by my_set_solver.
    repeat rewrite open_subst_same_value by my_set_solver. eauto.
  - rewrite open_subst_same_qualifier by my_set_solver. eauto.
Qed.

Lemma subst_open_td: forall (a: transducer) (x:atom) (u: value) (w: value) (k: nat),
    lc w -> {x := w}a ({k ~a> u} a) = ({k ~a> {x := w}v u} ({x := w}a a)).
Proof.
  induction a; cbn; intros; eauto.
  f_equal. eauto using subst_open_qualifier.
  all:
  repeat
    match goal with
    | H : context [lc _ -> _] |- _ => rewrite H by my_set_solver; eauto
    end.
  - rewrite subst_open_qualifier by my_set_solver.
    repeat rewrite subst_open_value by my_set_solver. eauto.
  - rewrite subst_open_qualifier by my_set_solver. eauto.
Qed.

Lemma subst_open_td_closed:
  ∀ (a : transducer) (x : atom) (u w : value) (k : nat),
    closed_value u ->
    lc w → {x := w }a ({k ~a> u} a) = {k ~a> u} ({x := w }a a).
Proof.
  intros. rewrite subst_open_td; auto.
  rewrite (subst_fresh_value); eauto. set_solver.
Qed.


Lemma subst_open_var_td: forall x y (u: value) (a: transducer) (k: nat),
    x <> y -> lc u -> {x := u}a ({k ~a> y} a) = ({k ~a> y} ({x := u}a a)).
Proof.
  intros.
  rewrite subst_open_td; auto. simpl. rewrite decide_False; auto.
Qed.


Lemma subst_lc_td : forall x (u: value) (a: transducer),
    lc_td a -> lc u -> lc_td ({x := u}a a).
Proof.
  pose subst_lc_phi1.
  pose subst_lc_phi2.
  pose subst_lc_value.
  induction 1; intros Hu; eauto using lc_td.
  all: simpl; auto_exists_L; intros y Hy; specialize_with y;
       rewrite subst_open_var_td in *; eauto; set_solver.
Qed.

Lemma fv_of_subst_td_closed:
  forall x (u : value) (a: transducer),
    closed_value u ->
    td_fv ({x := u }a a) = (td_fv a ∖ {[x]}).
Proof.
  induction a; simpl; intros; eauto;
    repeat
      match goal with
      | H : closed_value _ -> td_fv _ = _ |- _ => rewrite H by my_set_solver; eauto
      end;
    repeat rewrite fv_of_subst_qualifier_closed by eauto;
    repeat rewrite fv_of_subst_value_closed by eauto;
    my_set_solver.
Qed.

Lemma open_not_in_eq_td (x : atom) (a : transducer): forall k,
  x # {k ~a> x} a ->
  forall e, a = {k ~a> e} a.
Proof.
  induction a; simpl; intros; eauto; f_equal;
        try (rewrite <- (open_not_in_eq_qualifier x) by my_set_solver; eauto);
        try (rewrite <- (open_not_in_eq_value x) by my_set_solver; eauto);
        try (auto_apply; my_set_solver).
Qed.

Lemma lc_subst_phi1:
  forall x (u: value) (ϕ: qualifier), lc_phi1 ({x := u}q ϕ) -> lc u -> lc_phi1 ϕ.
Proof.
  unfold lc_phi1. intros. simp_hyps.
  auto_exists_L. intros.
  ospecialize * H. my_set_solver.
  rewrite <- subst_open_var_qualifier in H by my_set_solver.
  eauto using lc_subst_qualifier.
Qed.

Lemma lc_subst_phi2:
  forall x (u: value) (ϕ: qualifier), lc_phi2 ({x := u}q ϕ) -> lc u -> lc_phi2 ϕ.
Proof.
  unfold lc_phi2. intros. simp_hyps.
  auto_exists_L. intros.
  ospecialize * (H x0 _ y). my_set_solver. my_set_solver.
  repeat rewrite <- subst_open_var_qualifier in H by my_set_solver.
  apply lc_subst_qualifier in H; eauto.
Qed.

Lemma lc_subst_td:
  forall x (u: value) (a: transducer), lc_td ({x := u}a a) -> lc u -> lc_td a.
Proof.
  pose lc_subst_phi1.
  pose lc_subst_phi2.
  pose lc_subst_value.
  intros.
  remember (({x:=u}a) a).
  generalize dependent a.
  induction H; intros;
      match goal with
      | H : _ = {_:=_}a ?a |- _ => destruct a; simpl in *; simplify_eq
      end; eauto using lc_td.
  - auto_exists_L. intros x0 Hx0. repeat specialize_with x0.
    auto_apply; eauto.
    rewrite <- subst_open_var_td by my_set_solver. eauto.
  - auto_exists_L. intros x0 Hx0. repeat specialize_with x0.
    auto_apply; eauto.
    rewrite <- subst_open_var_td by my_set_solver. eauto.
Qed.

Lemma open_td_idemp: forall u (v: value) (a: transducer) (k: nat),
    lc v ->
    {k ~a> u} ({k ~a> v} a) = ({k ~a> v} a).
Proof.
  pose open_qualifier_idemp.
  pose open_value_idemp.
  induction a; intros; simpl; f_equal; eauto.
Qed.

Lemma subst_intro_td: ∀ (A: transducer) (x : atom) (w : value) (k : nat),
    x # A → lc w → ({x:=w}a) ({k ~a> x} A) = {k ~a> w} A.
Proof.
  intros.
  specialize (subst_open_td A x x w k) as J.
  simpl in J. rewrite decide_True in J; auto.
  rewrite J; auto. rewrite subst_fresh_td; auto.
Qed.

Lemma lc_phi1_body: ∀ n vals prop,
    lc_phi1 (@qual n vals prop) -> Vector.Forall (fun v => body (treturn v)) vals.
Proof.
  intros. subst. sinvert H.
  rewrite Vector.Forall_forall. intros.
  auto_exists_L. intros.
  ospecialize * (H0 x0). my_set_solver.
  sinvert H0.
  apply Classical_Prop.EqdepTheory.inj_pair2 in H4.
  apply Classical_Prop.EqdepTheory.inj_pair2 in H5.
  subst.
  rewrite VectorSpec.Forall_map in H3.
  rewrite Vector.Forall_forall in H3. eauto.
Qed.

Lemma lc_phi2_body: ∀ n vals prop,
    lc_phi2 (@qual n vals prop) ->
    Vector.Forall (fun v =>
                     exists (L : aset), (forall (x : atom), x ∉ L -> forall (y : atom), y ∉ L -> lc ({0 ~v> y} ({1 ~v> x} v)))) vals.
Proof.
  intros. subst. sinvert H.
  rewrite Vector.Forall_forall. intros.
  auto_exists_L. intros.
  ospecialize * (H0 x0 _ y). my_set_solver. my_set_solver.
  sinvert H0.
  apply Classical_Prop.EqdepTheory.inj_pair2 in H5.
  apply Classical_Prop.EqdepTheory.inj_pair2 in H6.
  subst.
  repeat rewrite VectorSpec.Forall_map in H4.
  rewrite Vector.Forall_forall in H4. eauto.
Qed.

(* NOTE: Very very annoying, a reverse version of map_ext, using classical logic *)
Lemma vector_map_ext_in' {A B: Type} (f g: A -> B) {n: nat} (vec: vec A n):
  vmap f vec = vmap g vec -> (forall x, @Vector.In A x n vec -> f x = g x).
Proof.
  induction vec; simpl; intros.
  - inversion H0.
  - sinvert H.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H3.
    sinvert H0; eauto.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H5. subst.
    eapply IHvec in H3; eauto.
Qed.

Lemma fact1_value_twice: forall (u v1 v2: value) (e: value) i j1 j2,
    i <> j1 -> i <> j2 -> j1 <> j2 ->
    {i ~v> u} ({j1 ~v> v1} ({j2 ~v> v2} e)) = {j1 ~v> v1} ({j2 ~v> v2} e) -> {i ~v> u} e = e.
Proof.
  intros.
  assert ({i ~v> u} ({j2 ~v> v2} e) = {j2 ~v> v2} e).
  apply fact1_value with (j := j1) (v:= v1); eauto.
  apply fact1_value with (j := j2) (v:= v2); eauto.
Qed.

Lemma fact1_qualifier: forall (u v: value) (ϕ: qualifier) i j,
    i <> j -> {i ~q> u} ({j ~q> v} ϕ) = {j ~q> v} ϕ -> {i ~q> u} ϕ = ϕ.
Proof.
  intros.
  destruct ϕ. simpl. f_equal.
  rewrite <- Vector.map_id.
  apply Vector.map_ext_in.
  simpl in H0. sinvert H0.
  apply Classical_Prop.EqdepTheory.inj_pair2 in H2.
  rewrite Vector.map_map in H2.
  intros.
  eapply vector_map_ext_in' in H2; eauto.
  pose fact1_value; eauto.
Qed.

Lemma fact1_qualifier_twice: forall (u v1 v2: value) (ϕ: qualifier) i j1 j2,
    i <> j1 -> i <> j2 -> j1 <> j2 ->
    {i ~q> u} ({j1 ~q> v1} ({j2 ~q> v2} ϕ)) = {j1 ~q> v1} ({j2 ~q> v2} ϕ) -> {i ~q> u} ϕ = ϕ.
Proof.
  intros.
  assert ({i ~q> u} ({j2 ~q> v2} ϕ) = {j2 ~q> v2} ϕ).
  apply fact1_qualifier with (j := j1) (v:= v1); eauto.
  apply fact1_qualifier with (j := j2) (v:= v2); eauto.
Qed.

Lemma open_rec_lc_phi1: ∀ (u : value) ϕ (k : nat), lc_phi1 ϕ -> {S k ~q> u} ϕ = ϕ.
Proof.
  intros. destruct ϕ. apply lc_phi1_body in H.
  simpl. f_equal.
  rewrite <- Vector.map_id.
  apply Vector.map_ext_in.
  intros.
  rewrite Vector.Forall_forall in H.
  ospecialize * H; eauto.
  destruct H.
  auto_pose_fv y.
  apply fact1_value with (j := 0) (v:= y). lia.
  rewrite open_rec_lc_value; eauto. apply H. my_set_solver.
Qed.

(* NOTE: Very very annoying, when qualifier has builtin 1 or 2 arguments. *)
Lemma open_rec_lc_phi2: ∀ (u : value) ϕ (k : nat), lc_phi2 ϕ -> {S (S k) ~q> u} ϕ = ϕ.
Proof.
  intros. destruct ϕ. apply lc_phi2_body in H.
  simpl. f_equal.
  rewrite <- Vector.map_id.
  apply Vector.map_ext_in.
  intros.
  rewrite Vector.Forall_forall in H.
  ospecialize * H; eauto.
  destruct H.
  auto_pose_fv y1. auto_pose_fv y2.
  ospecialize * (H y1 _ y2); eauto. my_set_solver. my_set_solver.
  eapply (fact1_value_twice _ y1 y2 _ _ 0 1); eauto.
  rewrite open_rec_lc_value; eauto.
Qed.

Lemma fact1_td: forall (u v: value) (A: transducer) i j,
    i <> j -> {i ~a> u} ({j ~a> v} A) = {j ~a> v} A -> {i ~a> u} A = A.
Proof.
  pose fact1_value.
  pose fact1_qualifier.
  intros u v. induction A; simpl; intros; eauto; f_equal; simp_hyps; eauto.
  { apply fact1_qualifier in H0; eauto. }
  all: sinvert H0; apply fact1_qualifier in H2; eauto.
Qed.

Lemma open_rec_lc_td_aux (u : value) m: forall A (k : nat), td_measure A ≤ m -> lc_td A -> {k ~a> u} A = A.
Proof.
  pose open_rec_lc_phi1.
  pose open_rec_lc_phi2.
  induction m; simpl; intros A k Hm H; sinvert H; simpl in *; sinvert Hm; eauto;
    f_equal; eauto; try (rewrite open_rec_lc_value; eauto);
    try (rewrite IHm; eauto; lia).
  - auto_pose_fv x. apply fact1_td with (j := 0) (v := x); eauto.
    rewrite IHm; eauto. rewrite <- open_preserves_td_measure; eauto. apply H0. my_set_solver.
  - auto_pose_fv x. apply fact1_td with (j := 0) (v := x); eauto.
    rewrite IHm; eauto. rewrite <- open_preserves_td_measure; eauto. lia. apply H0. my_set_solver.
  - auto_pose_fv x. apply fact1_td with (j := 0) (v := x); eauto.
    rewrite IHm; eauto. rewrite <- open_preserves_td_measure; eauto. apply H0. my_set_solver.
  - auto_pose_fv x. apply fact1_td with (j := 0) (v := x); eauto.
    rewrite IHm; eauto. rewrite <- open_preserves_td_measure; eauto. lia. apply H0. my_set_solver.
Qed.

Lemma open_rec_lc_td: ∀ (u : value) A (k : nat), lc_td A -> {k ~a> u} A = A.
Proof.
  pose open_rec_lc_phi1.
  pose open_rec_lc_phi2.
  intros. generalize dependent k.
  induction H; simpl; intros; auto; f_equal; eauto;
    try (rewrite open_rec_lc_value; eauto).
  - auto_pose_fv x. apply fact1_td with (j := 0) (v := x); eauto.
    rewrite H0; eauto. my_set_solver.
  - auto_pose_fv x. apply fact1_td with (j := 0) (v := x); eauto.
    rewrite H0; eauto. my_set_solver.
Qed.

Lemma lc_tdEx_destruct: forall b ϕ A, lc_td (tdEx b ϕ A) <-> lc_phi1 ϕ /\ body_td A.
Proof.
  split; intros.
  - sinvert H. intuition. eexists L. eauto.
  - destruct H. destruct H0. auto_exists_L.
Qed.

Lemma lc_tdExArr_destruct: forall T1 T2 A, lc_td (tdExArr T1 T2 A) <-> body_td A.
Proof.
  split; intros.
  - sinvert H. intuition. eexists L. eauto.
  - destruct H. auto_exists_L.
Qed.

Lemma lc_tdComp_destruct: forall A B, lc_td (tdComp A B) <-> lc_td A /\ lc_td B.
Proof.
  split; intros.
  - sinvert H. intuition.
  - econstructor; intuition.
Qed.

Lemma body_td_comp: forall A B, body_td (tdComp A B) <-> body_td A /\ body_td B.
Proof.
  split; intros.
  - sinvert H. split; auto_exists_L; intros.
    + ospecialize * (H0 x0); eauto. my_set_solver.
      simpl in *; rewrite lc_tdComp_destruct in H0; intuition.
    + ospecialize * (H0 x0); eauto. my_set_solver.
      simpl in *; rewrite lc_tdComp_destruct in H0; intuition.
  - unfold body_td in H. simp_hyp H.
    auto_exists_L; intros. simpl. rewrite lc_tdComp_destruct. intuition; auto_apply; my_set_solver.
Qed.
