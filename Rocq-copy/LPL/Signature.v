(** * Opaque syntactic carriers and executable checks.
    Semantic truth and state equality require no decision procedures. *)
From Stdlib Require Import List.

Module Type LANGUAGE.
  (** This module type is the syntactic interface that an instance implements.
      Atoms and actions are opaque carriers; a [world_term] names a state
      in a label. Instance-specific payload structure stays in the instance. *)
  Parameter atom binder action world_term relation_symbol : Type.
  (** [{x=y}+{x<>y}] is a decision carrying a proof in either branch. These
      decisions let later checkers compare syntax without deciding whether
      any proposition holds in a semantic state. *)
  Parameter atom_eq_dec : forall x y : atom, {x=y}+{x<>y}.
  Parameter binder_eq_dec : forall x y : binder, {x=y}+{x<>y}.
  Parameter action_eq_dec : forall x y : action, {x=y}+{x<>y}.
  Parameter world_term_eq_dec : forall x y : world_term, {x=y}+{x<>y}.
  Parameter relation_eq_dec : forall x y : relation_symbol, {x=y}+{x<>y}.
  (** Checks ending in [wfb] return Booleans for use by executable generators.
      Atom/action checks validate payloads. Extension checks receive the
      body's [pureb] result, and custom relations receive their arity. The
      shared syntax checker separately checks all recursive children. *)
  Parameter atom_wfb : atom -> bool.
  Parameter extension_wfb : binder -> bool -> bool.
  Parameter action_wfb : action -> bool.
  Parameter world_term_wfb : world_term -> bool.
  Parameter custom_relation_wfb : relation_symbol -> nat -> bool.
  (** [world_name x] embeds a bare name into the instance's world terms.
      [world_support u] lists names on which [u] may depend; it is used for
      eigenvariable freshness. [subst_world x replacement u] substitutes in
      [u]. Semantics.v requires interpretation laws connecting these three
      syntactic operations to environment lookup and update. *)
  Parameter world_name : nat -> world_term.
  Parameter world_support : world_term -> list nat.
  Parameter subst_world : nat -> world_term -> world_term -> world_term.
End LANGUAGE.
