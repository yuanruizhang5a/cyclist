(** * Append labels, sorted relation endpoints, and custom relation payloads. *)
From Stdlib Require Import List Bool.
From CyclistRocq.LPL.Benchmarks.PPL Require Import Support.
Import ListNotations.
Definition two_world : world M.
Proof. refine (World M (fun x => if Nat.eqb x 0 then Idle else Held) (fun _ => [Idle;Held]) _); discriminate. Defined.
Example distinct_states_append : eval_label M two_world (Join l0 l1) = [Idle;Held]. Proof. reflexivity. Qed.
Example stutter_not_collapsed : eval_label M two_world (Join l0 l0) = [Idle;Idle]. Proof. reflexivity. Qed.
Example empty_left_unit : eval_label M two_world (Join Empty l0) = [Idle]. Proof. reflexivity. Qed.
Example empty_right_unit : eval_label M two_world (Join l0 Empty) = [Idle]. Proof. reflexivity. Qed.
Example empty_assertion_rejected : judgment_wfb (Jdg [] [assertion Empty Truth]) = false. Proof. reflexivity. Qed.
Definition edge := action_relation Acquire tt 0 1.
Example edge_holds : relation_holds M two_world edge.
Proof. apply action_relation_holds; split; [reflexivity|now left]. Qed.
Example long_trace_is_not_a_world_endpoint :
  ~ relation_holds M two_world (ActionRelation Acquire tt (TraceLabel 0) l1).
Proof. intros [s [t [H _]]]; discriminate. Qed.
Example same_state_custom_relation : relation_holds M two_world (CustomRelation SameState [l0;l0]).
Proof. exists Idle; reflexivity. Qed.
Example custom_arity_checked : relation_wfb (CustomRelation SameState [l0]) = false. Proof. reflexivity. Qed.
Example relation_substitution_is_sorted :
  map_labels (subst_world_label 0 2) (Rdg [edge] [] []) =
  Rdg [action_relation Acquire tt 2 1] [] []. Proof. reflexivity. Qed.
Example trace_substitution_reaches_relations :
  map_labels (subst_trace_label 0 (Join l0 l1)) (Rdg [ActionRelation Acquire tt (TraceLabel 0) l1] [] []) =
  Rdg [ActionRelation Acquire tt (Join l0 l1) l1] [] []. Proof. reflexivity. Qed.
Example differing_relations_block_backlinks : backlink_eqb (Rdg [edge] [] []) (Rdg [] [] []) = false.
Proof. reflexivity. Qed.
Print Assumptions edge_holds.
