From Stdlib Require Import List ZArith Lia.
From CyclistRocq.LPL.Benchmarks Require Import Support.
Import ListNotations Generation Cert.

Definition different_world : world M.
Proof.
  refine (World M (fun n => if Nat.eqb n 0 then constant_state 0 else constant_state 1)
    (fun _ => [constant_state 0]) _); discriminate.
Defined.
Example empty_left_unit : eval_label M different_world (Join Empty l0) = eval_label M different_world l0.
Proof. reflexivity. Qed.
Example empty_right_unit : eval_label M different_world (Join l0 Empty) = eval_label M different_world l0.
Proof. reflexivity. Qed.
Example same_state_stutters : eval_label M different_world (Join l0 l0) = [constant_state 0; constant_state 0].
Proof. reflexivity. Qed.
Example different_states_retained : eval_label M different_world (Join l0 l1) = [constant_state 0; constant_state 1].
Proof. reflexivity. Qed.
Example different_states_admissible : label_admissible M different_world (Join l0 l1).
Proof. discriminate. Qed.
Example empty_complete_rejected : judgment_wfb (Jdg [] [assertion Empty Truth]) = false.
Proof. reflexivity. Qed.
Example empty_axiom_rejected : someb (generate_axiom (Jdg [] [assertion Empty Truth])) = false.
Proof. vm_compute; reflexivity. Qed.
Example unit_component_accepted : judgment_wfb (Jdg [] [assertion (Join Empty l0) Truth]) = true.
Proof. reflexivity. Qed.
Example overlap_requires_matching_endpoint :
  ~ overlap M [constant_state 0] [constant_state 1;constant_state 1] [constant_state 0;constant_state 1].
Proof.
  intro H; apply overlap_list_singleton in H as [tail [Heq _]].
  injection Heq as Hstate Htail. apply (f_equal (fun s : state M => s 0)) in Hstate; discriminate.
Qed.
Example overlap_retains_one_endpoint :
  overlap M [constant_state 0;constant_state 1] [constant_state 1;constant_state 0]
    [constant_state 0;constant_state 1;constant_state 0].
Proof. exists [constant_state 0], (constant_state 1), [constant_state 0]; auto. Qed.

Definition root := Jdg [] [assertion (Join Empty l0) Truth].
Definition ax := generated_axiom root ltac:(vm_compute; reflexivity).
Theorem unit_label_valid : Cyclic.Valid root.
Proof. exact (raw_check_sound (axiom_graph ax) empty_trace_witness (axiom_graph_raw_check ax)). Qed.
Example nonvacuity : exists w, admissible M root w.
Proof. apply root_nonvacuous; reflexivity. Qed.
Print Assumptions unit_label_valid.
