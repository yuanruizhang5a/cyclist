(** * All four relational action rules, through generated graph certificates. *)
From Stdlib Require Import List Bool Arith String.
From CyclistRocq.LPL.Benchmarks.PPL Require Import Support.
Import ListNotations Generation Cert.
Open Scope string_scope.
Definition edge := action_relation Acquire tt 0 1.
Definition extended := action_label Empty 0 1.

Definition br_root := Jdg [assertion l0 safe]
  [assertion (Join Empty l0) (Box (act Acquire) (First safe))].
Definition br := requested br_root (AtomicEigen OnRight 0 1) ltac:(vm_compute; reflexivity).
Definition br_after := premise_at br 0.
Definition br_head := Rdg br_after.(relations) br_after.(antecedent) [assertion (Join l0 l1) (First safe)].
Definition br_unit := requested br_after (UnitLabels br_head [false] true true) ltac:(vm_compute; reflexivity).
Definition br_first := requested br_head (Local OnRight 0 "First.R") ltac:(vm_compute; reflexivity).
Definition br_leaf := premise_at br_first 0.
Definition br_ax := generated_axiom br_leaf ltac:(vm_compute; reflexivity).
Definition br_build := Cyclic.run_script br_root [Cyclic.ApplyRule 0 br;Cyclic.ApplyRule 1 br_unit;
  Cyclic.ApplyRule 2 br_first;Cyclic.CloseWith 3 br_ax].
Theorem atomic_box_right_valid : Cyclic.Valid br_root.
Proof. apply (raw_check_sound br_build.(Cyclic.built_graph) empty_trace_witness); vm_compute; reflexivity. Qed.
Example br_exact_premise : br_after = Rdg [edge] [assertion l0 safe] [assertion extended (First safe)].
Proof. reflexivity. Qed.

Definition bl_root := Rdg [edge] [assertion (Join Empty l0) (Box (act Acquire) safe)] [assertion extended safe].
Definition bl := requested bl_root (AtomicUse OnLeft 0 0) ltac:(vm_compute; reflexivity).
Definition bl_leaf := premise_at bl 0.
Definition bl_ax := generated_axiom bl_leaf ltac:(vm_compute; reflexivity).
Definition bl_build := Cyclic.run_script bl_root [Cyclic.ApplyRule 0 bl;Cyclic.CloseWith 1 bl_ax].
Theorem atomic_box_left_valid : Cyclic.Valid bl_root.
Proof. apply (raw_check_sound bl_build.(Cyclic.built_graph) empty_trace_witness); vm_compute; reflexivity. Qed.
Example bl_consumes_relation : bl_leaf = Jdg [assertion extended safe] [assertion extended safe]. Proof. reflexivity. Qed.

Definition dr_root := Rdg [edge] [assertion extended safe]
  [assertion (Join Empty l0) (Diamond (act Acquire) safe)].
Definition dr := requested dr_root (AtomicUse OnRight 0 0) ltac:(vm_compute; reflexivity).
Definition dr_leaf := premise_at dr 0.
Definition dr_ax := generated_axiom dr_leaf ltac:(vm_compute; reflexivity).
Definition dr_build := Cyclic.run_script dr_root [Cyclic.ApplyRule 0 dr;Cyclic.CloseWith 1 dr_ax].
Theorem atomic_diamond_right_valid : Cyclic.Valid dr_root.
Proof. apply (raw_check_sound dr_build.(Cyclic.built_graph) empty_trace_witness); vm_compute; reflexivity. Qed.
Example dr_consumes_relation : dr_leaf = Jdg [assertion extended safe] [assertion extended safe]. Proof. reflexivity. Qed.

Definition dl_root := Jdg [assertion (Join Empty l0) (Diamond (act Acquire) safe)] [assertion l0 safe].
Definition dl := requested dl_root (AtomicEigen OnLeft 0 1) ltac:(vm_compute; reflexivity).
Definition dl_after := premise_at dl 0.
Definition dl_head := Rdg dl_after.(relations) [assertion (Join l0 l1) safe] dl_after.(succedent).
Definition dl_unit := requested dl_after (UnitLabels dl_head [false] true true) ltac:(vm_compute; reflexivity).
Definition dl_at := requested dl_head (Local OnLeft 0 "At.L") ltac:(vm_compute; reflexivity).
Definition dl_leaf := premise_at dl_at 0.
Definition dl_ax := generated_axiom dl_leaf ltac:(vm_compute; reflexivity).
Definition dl_build := Cyclic.run_script dl_root [Cyclic.ApplyRule 0 dl;Cyclic.ApplyRule 1 dl_unit;
  Cyclic.ApplyRule 2 dl_at;Cyclic.CloseWith 3 dl_ax].
Theorem atomic_diamond_left_valid : Cyclic.Valid dl_root.
Proof. apply (raw_check_sound dl_build.(Cyclic.built_graph) empty_trace_witness); vm_compute; reflexivity. Qed.

Example stale_successor_rejected : someb (generate_requested br_root (AtomicEigen OnRight 0 0)) = false.
Proof. vm_compute; reflexivity. Qed.
Definition unrelated_relation_goal := Rdg [CustomRelation SameState [StateLabel 2;StateLabel 2]]
  [assertion l0 safe] [assertion (Join Empty l0) (Box (act Acquire) (First safe))].
Example freshness_scans_relation_arguments : someb (generate_requested unrelated_relation_goal (AtomicEigen OnRight 0 2)) = false.
Proof. vm_compute; reflexivity. Qed.
Definition wrong_action := Rdg [action_relation Stutter tt 0 1] bl_root.(antecedent) bl_root.(succedent).
Example wrong_action_rejected : someb (generate_requested wrong_action (AtomicUse OnLeft 0 0)) = false.
Proof. vm_compute; reflexivity. Qed.
Definition wrong_source := Rdg [action_relation Acquire tt 1 0] bl_root.(antecedent) bl_root.(succedent).
Example wrong_source_rejected : someb (generate_requested wrong_source (AtomicUse OnLeft 0 0)) = false.
Proof. vm_compute; reflexivity. Qed.
Example missing_relation_rejected : someb (generate_requested (Jdg dr_root.(antecedent) dr_root.(succedent)) (AtomicUse OnRight 0 0)) = false.
Proof. vm_compute; reflexivity. Qed.
Example finite_scan_includes_action_rule :
  existsb (fun r => String.eqb r.(Cyclic.rule_name) "B.Atomic.R") (generate_rules br_root) = true.
Proof. vm_compute; reflexivity. Qed.
Example nonvacuity : exists w, admissible M br_root w.
Proof. apply root_nonvacuous; reflexivity. Qed.
Definition transition_world : world M.
Proof. refine (World M (fun x => if Nat.eqb x 0 then Idle else Held) (fun _ => [Idle]) _); discriminate. Defined.
Example live_transition : relations_hold M transition_world [edge].
Proof. constructor; [apply action_relation_holds; split; auto|constructor]. Qed.
Example live_antecedent : left_holds M transition_world dr_root.(antecedent).
Proof. repeat constructor; discriminate. Qed.
Print Assumptions atomic_box_right_valid.
Print Assumptions atomic_box_left_valid.
Print Assumptions atomic_diamond_right_valid.
Print Assumptions atomic_diamond_left_valid.
Print Assumptions box_atomic_right.

Example br_graph_nodes : List.length br_build.(Cyclic.built_graph).(Cyclic.graph_nodes) = 4.
Proof. vm_compute; reflexivity. Qed.
Example br_tag_count : List.length (Cyclic.all_graph_tags br_build.(Cyclic.built_graph)) = 0.
Proof. vm_compute; reflexivity. Qed.

Example bl_graph_nodes : List.length bl_build.(Cyclic.built_graph).(Cyclic.graph_nodes) = 2.
Proof. vm_compute; reflexivity. Qed.
Example bl_tag_count : List.length (Cyclic.all_graph_tags bl_build.(Cyclic.built_graph)) = 0.
Proof. vm_compute; reflexivity. Qed.

Example dr_graph_nodes : List.length dr_build.(Cyclic.built_graph).(Cyclic.graph_nodes) = 2.
Proof. vm_compute; reflexivity. Qed.
Example dr_tag_count : List.length (Cyclic.all_graph_tags dr_build.(Cyclic.built_graph)) = 0.
Proof. vm_compute; reflexivity. Qed.

Example dl_graph_nodes : List.length dl_build.(Cyclic.built_graph).(Cyclic.graph_nodes) = 4.
Proof. vm_compute; reflexivity. Qed.
Example dl_tag_count : List.length (Cyclic.all_graph_tags dl_build.(Cyclic.built_graph)) = 0.
Proof. vm_compute; reflexivity. Qed.
