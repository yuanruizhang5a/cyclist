From Stdlib Require Import List.

(** Finitary, single-sorted signatures. Equality is required only for syntax;
    models need neither decidable equality nor decidable predicate truth. *)
Module Type SIGNATURE.
  Parameter function_symbol predicate_symbol : Type.
  Parameter function_eq_dec : forall x y : function_symbol, {x = y} + {x <> y}.
  Parameter predicate_eq_dec : forall x y : predicate_symbol, {x = y} + {x <> y}.
  Parameter function_arity : function_symbol -> nat.
  Parameter predicate_arity : predicate_symbol -> nat.
End SIGNATURE.
