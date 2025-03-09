From stdpp Require Import mapset.
From CT Require Import CoreLang.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import Qualifier.
From CT Require Import RefinementType.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import OperationalSemantics.
Import BasicTyping.
Import RefinementType.

(** This file defines valuation environment, i.e., substitution (σ), and
  multi-substitution operation. *)

(** Environment (substitution) *)
Notation env := (amap value).

Inductive epr : Type :=
| Epr (σ: env) (L: aset) (Σ: env -> Prop).

Definition closed_env (env : env) := map_Forall (fun _ => closed_value) env.
Inductive closed_epr: epr -> Prop :=
| Closed_epr: forall (σ: env) (L: aset) (Σ: env -> Prop),
    dom σ ∩ L = ∅ ->
    closed_env σ ->
    (forall σ', Σ σ' -> closed_env σ /\ dom σ' = L) ->
    closed_epr (Epr σ L Σ).

Definition eprdom (epr: epr) :=
  match epr with
  | Epr σ L _ => dom σ ∪ L
  end.

Inductive eprR: epr -> env -> Prop :=
| EprR: forall σ1 σ2 L Σ, Σ σ2 -> eprR (Epr σ1 L Σ) (σ1 ∪ σ2).

#[global]
  Instance epr_stale {A:Type} : Stale epr := eprdom.
Arguments epr_stale /.

(** Multi-substitution, i.e., σ(⋅) operation. The definition is parameterized by
  any substitution. *)
Definition msubst {A} (subst : atom -> value -> A -> A)
                  (env : env) (a : A) : A :=
  map_fold subst a env.

Notation "'m{' x '}q'" := (msubst qualifier_subst x) (at level 20, format "m{ x }q", x constr).
Notation "'m{' x '}r'" := (msubst rty_subst x) (at level 20, format "m{ x }r", x constr).
Notation "'m{' x '}v'" := (msubst value_subst x) (at level 20, format "m{ x }v", x constr).
Notation "'m{' x '}t'" := (msubst tm_subst x) (at level 20, format "m{ x }t", x constr).
