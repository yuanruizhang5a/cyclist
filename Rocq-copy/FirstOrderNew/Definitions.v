From Stdlib Require Import List Bool Arith String.
From CyclistRocq.FirstOrderNew Require Export Substitution.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Record clause := { clause_name : string; head : list term; body : product }.
Definition definitions := list clause.
Definition clauses_for d name := filter (fun c => String.eqb c.(clause_name) name) d.
Definition clause_vars c := List.concat (map term_vars c.(head)) ++ product_vars c.(body).
Definition subst_clause s c := {| clause_name := c.(clause_name);
  head := map (subst_term s) c.(head); body := subst_product s c.(body) |}.
Definition freshen_clause avoid c := subst_clause (freshening avoid (clause_vars c)) c.
Definition definedb d p arity := existsb
  (fun c => String.eqb c.(clause_name) p && Nat.eqb (List.length c.(head)) arity) d.
Fixpoint term_wfb t :=
  match t with
  | Fun f ts =>
    (if String.eqb f "s" then Nat.eqb (List.length ts) 1
     else if String.eqb f "cons" then Nat.eqb (List.length ts) 2 else true)
    && forallb term_wfb ts
  | _ => true end.
Definition atom_wfb d a :=
  match a with Eq t u | Deq t u => term_wfb t && term_wfb u
  | Pred _ p ts => definedb d p (List.length ts) && forallb term_wfb ts end.
Definition definition_errors d := flat_map
  (fun c => flat_map
    (fun a => match a with
      | Pred _ p ts => if definedb d p (List.length ts) then [] else [p]
      | _ => [] end) c.(body)) d.
Definition definitions_wfb d :=
  forallb (fun c => forallb term_wfb c.(head) &&
    forallb (atom_wfb d) c.(body) &&
    forallb (fun c' => if String.eqb c.(clause_name) c'.(clause_name)
      then Nat.eqb (List.length c.(head)) (List.length c'.(head)) else true) d) d.
Definition sequent_wfb d j := antecedent_freeb j &&
  forallb (forallb (atom_wfb d)) (j.(antecedent) ++ j.(succedent)).

Example missing_predicate_is_diagnosed :
  definition_errors [{| clause_name := "MUL"; head := [];
    body := [Pred 0 "ADD_2" []] |}] = ["ADD_2"].
Proof. reflexivity. Qed.
