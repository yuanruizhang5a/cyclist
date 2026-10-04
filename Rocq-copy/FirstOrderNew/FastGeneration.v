From Stdlib Require Import List Bool Arith.
From CyclistRocq.FirstOrderNew Require Export Compiler.
Import ListNotations.
Open Scope list_scope.

(** The original optimized right-unfold rule does not expand a constructor head
    against a universal variable. Unrestricted equation fallback creates an
    infinite search prefix before left unfolding. Keep the source restriction;
    equation fallback is useful only for explicitly existential RHS witnesses.

    checked_apply still compiles EVERY application and checks exact expected
    labels. Filtering an entire macro menu by recompiling all its applications
    beforehand is redundant, and defeats demand-driven DFS. *)
Definition fast_right_family limits d j := firstn limits.(candidate_limit)
  (compiled_right_unfold_proposals limits d j ++
   if existsb (fun v => negb (is_free v)) (formula_vars j.(succedent))
   then compiled_right_fallback_proposals limits d j else []).
Definition fast_combined limits d j :=
  bounded_bind limits.(combination_limit) (fun p =>
    bind_program limits.(combination_limit) (fun k =>
      match compiled_simplification_proposal d k with
      | Some _ => []
      | None => map (compiled_wrapped_program limits d) (fast_right_family limits d k)
      end) (compiled_wrapped_program limits d p))
    (compiled_left_unfold_proposals limits d j).
Definition fast_choice_programs limits d idx j nodes :=
  map ProgramBacklink (compiled_backlink_plans limits d idx j nodes) ++
  map (compiled_wrapped_program limits d) (compiled_left_split_proposals d j) ++
  map (compiled_wrapped_program limits d) (compiled_instantiation_proposals limits d j) ++
  map (compiled_wrapped_program limits d) (compiled_right_split_proposals limits d j) ++
  map (compiled_wrapped_program limits d) (fast_right_family limits d j) ++
  fast_combined limits d j ++
  map (compiled_wrapped_program limits d) (compiled_left_unfold_proposals limits d j) ++
  compiled_fold_backlink_programs limits d j nodes.
Definition fast_source_menu limits d idx j nodes :=
  match compiled_axiom_proposals d j with
  | p::ps => {| menu_axioms := map primitive_program (p::ps);
               menu_simplifications := []; menu_choices := [] |}
  | [] => match compiled_simplification_proposal d j with
    | Some p => {| menu_axioms := []; menu_simplifications := [compiled_wrapped_program limits d p];
                  menu_choices := [] |}
    | None => {| menu_axioms := []; menu_simplifications := [];
                menu_choices := fast_choice_programs limits d idx j nodes |}
    end end.
