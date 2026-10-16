From Stdlib Require Import List Bool Arith ZArith String.
From CyclistRocq.LPL.Benchmarks Require Import Support.
Import ListNotations Generation Cert.
Open Scope string_scope.
Open Scope list_scope.

(** A real star cycle: an initial-state observation remains true while an
    arbitrary finite number of increments execute. This is a prefix property;
    the separate counter-loop benchmark checks every visited state. *)
Definition action := Assign 0 (inc x).
Definition body := First nonnegative.
Definition prefix := Join l0 (TraceLabel 0).
Definition root := Jdg [assertion l0 nonnegative]
  [traced (Join prefix l1) (Box (Star action) body) 0].
Definition star_rule := requested root (Local OnRight 0 "B.Star.R") ltac:(vm_compute; reflexivity).
Definition base_goal := premise_at star_rule 0.
Definition step_goal := premise_at star_rule 1.
Definition test_rule := requested base_goal (Local OnRight 0 "B.Test.R") ltac:(vm_compute; reflexivity).
Definition base_end := premise_at test_rule 0.
Definition base_mid := Jdg base_end.(antecedent)
  [assertion (Join (Join l0 (Join (TraceLabel 0) l1)) l1) body].
Definition base_head := Jdg base_end.(antecedent)
  [assertion (Join l0 (Join (Join (TraceLabel 0) l1) l1)) body].
Definition rotate_base_inner := requested base_end (RotateLabels base_mid [false] true) ltac:(vm_compute; reflexivity).
Definition rotate_base_outer := requested base_mid (RotateLabels base_head [] true) ltac:(vm_compute; reflexivity).
Definition first_rule := requested base_head (Local OnRight 0 "First.R") ltac:(vm_compute; reflexivity).
Definition leaf := premise_at first_rule 0.
Definition leaf_axiom := generated_axiom leaf ltac:(vm_compute; reflexivity).
Definition assignment_rule := requested step_goal (Local OnRight 0 "B.Assign.R") ltac:(vm_compute; reflexivity).
Definition after_assignment := premise_at assignment_rule 0.
Definition updated := AssignUpdate 0 (inc x) u1.
Definition after_world_sub := map_labels (subst_world_label 1 updated) root.
Definition after_trace_sub := map_labels (subst_trace_label 0 (Join (TraceLabel 0) l1)) after_world_sub.
Definition rotate_step := requested after_assignment (RotateLabels after_trace_sub [false] true) ltac:(vm_compute; reflexivity).
Definition trace_sub := requested after_trace_sub (SubstituteTrace after_world_sub 0 (Join (TraceLabel 0) l1)) ltac:(vm_compute; reflexivity).
Definition world_sub := requested after_world_sub (SubstituteWorld root 1 updated) ltac:(vm_compute; reflexivity).
Definition backlink := requested root (BacklinkExact root) ltac:(vm_compute; reflexivity).

Definition script := [Cyclic.ApplyRule 0 star_rule; Cyclic.ApplyRule 1 test_rule;
  Cyclic.ApplyRule 3 rotate_base_inner; Cyclic.ApplyRule 4 rotate_base_outer;
  Cyclic.ApplyRule 5 first_rule; Cyclic.CloseWith 6 leaf_axiom;
  Cyclic.ApplyRule 2 assignment_rule; Cyclic.ApplyRule 7 rotate_step;
  Cyclic.ApplyRule 8 trace_sub; Cyclic.ApplyRule 9 world_sub;
  Cyclic.AddBacklink 10 0 backlink].
Definition build := Cyclic.run_script root script.
Definition graph := build.(Cyclic.built_graph).
Definition witness : Cyclic.trace_witness :=
  {| Cyclic.witness_tag := fun i => match i with 0 | 2 | 7 | 8 | 9 | 10 => Some 0 | _ => None end;
     Cyclic.witness_potential := fun i => match i with
       0 => 2 | 2 => 1 | 7 => 6 | 8 => 5 | 9 => 4 | 10 => 3 | _ => 0 end |}.
Example script_succeeds : build.(Cyclic.build_ok) = true. Proof. vm_compute; reflexivity. Qed.
Example graph_size : List.length graph.(Cyclic.graph_nodes) = 11. Proof. vm_compute; reflexivity. Qed.
Example real_backlink :
  match Cyclic.node_at graph 10 with
  | Some n => match n.(Cyclic.node_payload) with
    | Cyclic.BacklinkNode _ target => Nat.eqb target 0
    | _ => false end
  | None => false end = true.
Proof. vm_compute; reflexivity. Qed.
Example accepted : Cyclic.raw_check graph witness = true. Proof. vm_compute; reflexivity. Qed.
Theorem star_prefix_invariant : Cyclic.Valid root.
Proof. exact (raw_check_sound graph witness accepted). Qed.
Example nonvacuity : exists w, admissible M root w.
Proof. apply root_nonvacuous; vm_compute; reflexivity. Qed.
Print Assumptions star_prefix_invariant.
