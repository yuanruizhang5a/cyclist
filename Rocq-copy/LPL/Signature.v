(** * The vocabulary of the object logic

    Start here, then read Syntax.v and Semantics.v. A [SIGNATURE] supplies
    names and argument counts; a semantic model later assigns meanings to
    those names. Keeping the two interfaces separate lets the same syntax be
    interpreted over integers, Booleans, or an arbitrary nonempty carrier. *)
From Stdlib Require Import List.

(** Finitary, single-sorted signatures. Equality is required only for syntax;
    models need neither decidable equality nor decidable predicate truth. *)
Module Type SIGNATURE.
  (** Function and predicate symbols occupy separate namespaces. A constant
      is simply a function symbol whose arity is zero. *)
  Parameter function_symbol predicate_symbol : Type.
  (** These decisions compare names in reified syntax. They make executable
      formula/judgment comparison possible without comparing model values. *)
  Parameter function_eq_dec : forall x y : function_symbol, {x = y} + {x <> y}.
  Parameter predicate_eq_dec : forall x y : predicate_symbol, {x = y} + {x <> y}.
  (** Syntax.v checks list lengths against these arities before a concrete
      rule instance can cross the well-formedness boundary. *)
  Parameter function_arity : function_symbol -> nat.
  Parameter predicate_arity : predicate_symbol -> nat.
End SIGNATURE.
