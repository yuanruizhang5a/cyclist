From Stdlib Require Import List Bool Arith Lia.

From CyclistRocq.SP Require Import Syntax Semantics.

Import ListNotations.

(** * Small verified automation utilities *)

Definition strict_self_constraintb (c : ordinal_constraint) : bool :=
  match c.(constraint_order) with
  | Strict => tag_eqb c.(constraint_left) c.(constraint_right)
  | NonStrict => false
  end.

Definition constraints_inconsistentb (cs : list ordinal_constraint) : bool :=
  existsb strict_self_constraintb cs.

Lemma constraints_inconsistentb_sound tau cs :
  constraints_inconsistentb cs = true -> ~ constraints_hold tau cs.
Proof.
  unfold constraints_inconsistentb. rewrite existsb_exists.
  intros [bad [Hin Hbad]] Hholds.
  induction cs as [|c rest IH]; simpl in *; [contradiction|].
  destruct Hholds as [Hc Hrest]. destruct Hin as [-> | Hin].
  - destruct bad as [left order right]. simpl in *.
    destruct order; try discriminate.
    apply tag_eqb_spec in Hbad.
    change (left = right) in Hbad. change (tau left < tau right) in Hc.
    rewrite <- Hbad in Hc.
    exact (Nat.lt_irrefl (tau left) Hc).
  - exact (IH Hin Hrest).
Qed.

(** A substitution accepted here never changes a free parameter. *)
Definition binding_existentialb (binding : variable * term) : bool :=
  match (fst binding).(variable_kind) with
  | Existential => true
  | Free => false
  end.

Definition existential_substitutionb (s : substitution) : bool :=
  forallb binding_existentialb s.

Definition fresh_free_variable (used_ids : list nat) : variable :=
  free_var (S (fold_right Nat.max 0 used_ids)).

Definition fresh_existential_variable (used_ids : list nat) : variable :=
  existential_var (S (fold_right Nat.max 0 used_ids)).

Definition fresh_free_tag (used_ids : list nat) : trace_tag :=
  FreeTag (S (fold_right Nat.max 0 used_ids)).

Definition normalization_candidate (j : judgment) : judgment :=
  normalize_judgment j.

Lemma normalization_candidate_sound j w :
  denote (normalization_candidate j) w <-> denote j w.
Proof. reflexivity. Qed.

Example strict_self_constraint_rejected :
  constraints_inconsistentb
    [lt_constraint (FreeTag 2) (FreeTag 2)] = true.
Proof. reflexivity. Qed.

Example nonstrict_self_constraint_allowed :
  constraints_inconsistentb
    [le_constraint (FreeTag 2) (FreeTag 2)] = false.
Proof. reflexivity. Qed.

Example free_binding_rejected :
  existential_substitutionb [(free_var 0, Nil)] = false.
Proof. reflexivity. Qed.
