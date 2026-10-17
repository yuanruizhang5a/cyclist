(** * Parameters of labelled process logic

    A language supplies only reified data and executable syntax checks.
    Semantic truth and state equality are deliberately absent here.

    Two atomic/extension slots preserve the existing first-order constructor
    interface without imposing first-order meanings on the shared theory.
    Plain PPL uses the first atomic slot, no extension tokens, and a unit
    action payload. Structured languages may use every slot. *)
From Stdlib Require Import List.

Module Type LANGUAGE.
  Parameter atom_symbol argument binder action_symbol action_argument world_term relation_symbol : Type.
  Parameter atom_eq_dec : forall x y : atom_symbol, {x=y}+{x<>y}.
  Parameter argument_eq_dec : forall x y : argument, {x=y}+{x<>y}.
  Parameter binder_eq_dec : forall x y : binder, {x=y}+{x<>y}.
  Parameter action_eq_dec : forall x y : action_symbol, {x=y}+{x<>y}.
  Parameter action_argument_eq_dec : forall x y : action_argument, {x=y}+{x<>y}.
  Parameter world_term_eq_dec : forall x y : world_term, {x=y}+{x<>y}.
  Parameter relation_eq_dec : forall x y : relation_symbol, {x=y}+{x<>y}.
  Parameter atom_wfb : atom_symbol -> list argument -> bool.
  Parameter binary_atom_wfb : argument -> argument -> bool.
  Parameter extension_wfb coextension_wfb : binder -> bool -> bool.
  Parameter action_wfb : action_symbol -> action_argument -> bool.
  Parameter world_term_wfb : world_term -> bool.
  Parameter custom_relation_wfb : relation_symbol -> nat -> bool.
  Parameter world_name : nat -> world_term.
  Parameter world_support : world_term -> list nat.
  Parameter subst_world : nat -> world_term -> world_term -> world_term.
End LANGUAGE.
