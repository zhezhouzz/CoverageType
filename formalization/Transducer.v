From stdpp Require Import mapset.
From stdpp Require Import natmap.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import Qualifier.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import OperationalSemantics.
Import BasicTyping.
Import Qualifier.
Import Trace.

(** This file defines the λᴱ refinement type syntax (Fig. 4). Like λᴱ term
  syntax, the type syntax also uses locally nameless representation. *)

(** Symbolic finite automata (A, B in Fig. 4). Only a minimal set of SFAs
  relevant to metatheory are formalized. The complete set of SFAs can be
  straightforwardly added, but it is orthogonal to the formal development. *)
  (** Qualifier [ϕ] may refer to two bound variables: [bvar 1] is the argument
  variable, [bvar 0] is result variable. *)

(** The transducer supports
    - identity
    - ⟨x_ret ← f x_arg | 𝜙⟩/id
    - ⟨x_ret ← f x_arg | 𝜙⟩/⟨v_ret ← f v_arg⟩
    - T . T
    - T \/ T
    - Ex x:b. T
 *)
Inductive transducer : Type :=
| tdId
| tdLitId (op: effop) (ϕ: qualifier)
| tdLitOut (op1: effop) (ϕ1: qualifier) (op2: effop) (arg2: value) (ret2: value)
| tdComp (td1: transducer) (td2: transducer)
| tdUnion (td1: transducer) (td2: transducer)
(* | tdStar (td: transducer) *)
| tdEx (b: base_ty) (ϕ: qualifier) (td: transducer)
| tdExArr (T1: ty) (T2: ty) (td: transducer).

(* Notation "'⟨' op '|' ϕ '⟩/ϵ'" := (tdLitEps op ϕ) (at level 5, format "⟨ op | ϕ ⟩/ϵ", op constr, ϕ constr). *)
Notation "'⟨' op '|' ϕ '⟩/id'" := (tdLitId op ϕ) (at level 5, format "⟨ op | ϕ ⟩/id", op constr, ϕ constr).
Notation "'⟨' op1 '|' ϕ1 '⟩/⟨' op2 '|' arg '|' ret '⟩'" := (tdLitOut op1 ϕ1 op2 arg ret) (at level 5, format "⟨ op1 | ϕ1 ⟩/⟨ op2 | arg | ret ⟩", op1 constr, ϕ1 constr, op2 constr, arg constr, ret constr).

Notation " a '○' b " := (tdComp a b) (at level 5, format "a ○ b", b constr, a constr, right associativity).

Global Hint Constructors transducer: core.

(** * Naming related definitions *)

(** free variables *)
Fixpoint td_fv a : aset :=
  match a with
  | tdId => ∅
  | tdLitId _ ϕ => qualifier_fv ϕ
  | tdLitOut _ ϕ1 _ arg ret => qualifier_fv ϕ1 ∪ fv_value arg ∪ fv_value ret
  | tdComp a1 a2 | tdUnion a1 a2 => td_fv a1 ∪ td_fv a2
  | tdEx _ ϕ a => qualifier_fv ϕ ∪ td_fv a
  | tdExArr _ _ a => td_fv a
  end.

#[global]
  Instance td_stale : @Stale aset transducer := td_fv.
Arguments td_stale /.

(* The effect operator always has 2 bound variables *)
Fixpoint td_open (k: nat) (s: value) (a : transducer): transducer :=
  match a with
  | tdId => tdId
  | tdLitId op ϕ => tdLitId op (qualifier_open (S (S k)) s ϕ)
  | tdLitOut op1 ϕ1 op2 arg ret => tdLitOut op1 (qualifier_open (S (S k)) s ϕ1) op2 (open_value k s arg) (open_value k s ret)
  | tdComp a1 a2 => tdComp (td_open k s a1) (td_open k s a2)
  | tdUnion a1 a2 => tdUnion (td_open k s a1) (td_open k s a2)
  | tdEx b ϕ a => tdEx b (qualifier_open (S k) s ϕ) (td_open (S k) s a)
  | tdExArr T1 T2 a => tdExArr T1 T2 (td_open (S k) s a)
  end.

Notation "'{' k '~a>' s '}' e" := (td_open k s e) (at level 20, k constr).
Notation "e '^a^' s" := (td_open 0 s e) (at level 20).

Fixpoint td_subst (k: atom) (s: value) (a : transducer): transducer :=
  match a with
  | tdId => tdId
  | tdLitId op ϕ => tdLitId op (qualifier_subst k s ϕ)
  | tdLitOut op1 ϕ1 op2 arg ret =>
      tdLitOut op1 (qualifier_subst k s ϕ1) op2 (value_subst k s arg) (value_subst k s ret)
  | tdComp a1 a2 => tdComp (td_subst k s a1) (td_subst k s a2)
  | tdUnion a1 a2 => tdUnion (td_subst k s a1) (td_subst k s a2)
  | tdEx b ϕ a => tdEx b (qualifier_subst k s ϕ) (td_subst k s a)
  | tdExArr T1 T2 a => tdExArr T1 T2 (td_subst k s a)
  end.

Notation "'{' x ':=' s '}a'" := (td_subst x s) (at level 20, format "{ x := s }a", x constr).

(** Local closure *)

Inductive lc_td : transducer -> Prop :=
| lc_tdId: lc_td tdId
| lc_tdLitId: forall op ϕ, lc_phi2 ϕ -> lc_td (tdLitId op ϕ)
| lc_tdLitOut: forall op1 ϕ1 op2 (arg ret: value), lc_phi2 ϕ1 -> lc arg -> lc ret -> lc_td (tdLitOut op1 ϕ1 op2 arg ret)
| lc_tdComp : forall a1 a2, lc_td a1 -> lc_td a2 -> lc_td (tdComp a1 a2)
| lc_tdUnion : forall a1 a2, lc_td a1 -> lc_td a2 -> lc_td (tdUnion a1 a2)
| lc_tdEx : forall b ϕ a (L : aset), (forall x : atom, x ∉ L -> lc_td (a ^a^ x)) -> lc_phi1 ϕ -> lc_td (tdEx b ϕ a)
| lc_tdExArr : forall T1 T2 a (L : aset), (forall x : atom, x ∉ L -> lc_td (a ^a^ x)) -> lc_td (tdExArr T1 T2 a)
.

Definition body_td A := exists (L: aset), ∀ x : atom, x ∉ L → lc_td (A ^a^ x).

(** Closed under free variable set *)

Inductive closed_td (d: aset) (a: transducer): Prop :=
| closed_td_: lc_td a -> td_fv a ⊆ d -> closed_td d a.

(* This measure function is used to guarantee termination of the denotation.
Instead of addtion, we can also use [max] for the subterms. *)
Fixpoint td_measure (a: transducer) : nat :=
  match a with
  | tdId => 1
  | ⟨ _ | _ ⟩/id | ⟨ _ | _ ⟩/⟨ _ | _ | _ ⟩ => 1
  | a1 ○ a2 | tdUnion a1 a2 => 1 + td_measure a1 + td_measure a2
  | tdEx _ _ a => 1 + td_measure a
  | tdExArr _ _ a => 1 + td_measure a
  end.

Lemma td_measure_gt_0 ρ : td_measure ρ > 0.
Proof.
  induction ρ; simpl; lia.
Qed.

Lemma td_measure_S ρ : exists n, td_measure ρ = S n.
Proof.
  destruct (Nat.lt_exists_pred 0 (td_measure ρ)).
  pose proof (td_measure_gt_0 ρ). lia.
  intuition eauto.
Qed.

Lemma open_preserves_td_measure ρ: forall k t,
    td_measure ρ = td_measure ({k ~a> t} ρ).
Proof.
  induction ρ; simpl; eauto.
Qed.

Lemma subst_preserves_td_measure ρ: forall x t,
    td_measure ρ = td_measure ({x:=t}a ρ).
Proof.
  induction ρ; simpl; eauto.
Qed.
