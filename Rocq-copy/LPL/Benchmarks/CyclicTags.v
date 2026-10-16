From Stdlib Require Import List Bool Arith.
From CyclistRocq.LPL.Benchmarks Require Import Support Cyclic.
Import ListNotations Generation Cert.
Module PrefixCycle := CyclistRocq.LPL.Benchmarks.Cyclic.
Definition root := PrefixCycle.root.
Definition retagged := rename_tags (rename_lookup [(0,7)]) root.
Definition forward := requested root (BacklinkTags [(0,7)] retagged) ltac:(vm_compute; reflexivity).
Definition backward := requested retagged (BacklinkTags [(7,0)] root) ltac:(vm_compute; reflexivity).
Definition script := firstn 10 PrefixCycle.script ++ [Cyclic.ApplyRule 10 forward;Cyclic.AddBacklink 11 0 backward].
Definition build := Cyclic.run_script root script.
Definition graph := build.(Cyclic.built_graph).
Definition witness : Cyclic.trace_witness :=
  {| Cyclic.witness_tag := fun i => match i with
       | 0 | 2 | 7 | 8 | 9 | 10 => Some 0 | 11 => Some 7 | _ => None end;
     Cyclic.witness_potential := fun i => match i with
       | 0 => 2 | 2 => 1 | 7 => 7 | 8 => 6 | 9 => 5 | 10 => 4 | 11 => 3 | _ => 0 end |}.
Example build_succeeds : build.(Cyclic.build_ok) = true. Proof. vm_compute; reflexivity. Qed.
Example graph_size : List.length graph.(Cyclic.graph_nodes) = 12. Proof. vm_compute; reflexivity. Qed.
Example checked : Cyclic.raw_check graph witness = true. Proof. vm_compute; reflexivity. Qed.
Theorem explicit_tag_renaming_cycle : Cyclic.Valid root.
Proof. exact (raw_check_sound graph witness checked). Qed.
Example nonvacuity : exists w, admissible M root w.
Proof. exact PrefixCycle.nonvacuity. Qed.
Print Assumptions explicit_tag_renaming_cycle.
