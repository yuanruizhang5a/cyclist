From Stdlib Require Import List Bool Arith String.

From CyclistRocq.FirstOrder Require Import
  Syntax Semantics Definitions Derived Rules.

Import ListNotations.
Open Scope string_scope.

Definition x : term := fv 0.
Definition y : term := fv 1.
Definition z : term := fv 2.

Definition benchmark_01 : judgment :=
  mk_judgment fo_definitions
    (mk_sequent [[tagged_pred 0 "O" [x]]] [[pred "N" [x]]]).

Definition benchmark_02 : judgment :=
  mk_judgment fo_definitions
    (mk_sequent [[tagged_pred 0 "E" [x]]; [tagged_pred 1 "O" [x]]]
      [[pred "N" [x]]]).

Definition benchmark_04 : judgment :=
  mk_judgment fo_definitions
    (mk_sequent [[tagged_pred 0 "N" [x]]]
      [[pred "O" [x]]; [pred "E" [x]]]).

Definition benchmark_05 : judgment :=
  mk_judgment fo_definitions
    (mk_sequent [[tagged_pred 0 "N" [x]; tagged_pred 1 "N" [y]]]
      [[pred "Q" [x; y]]]).

Definition benchmark_07 : judgment :=
  mk_judgment fo_definitions
    (mk_sequent [[tagged_pred 0 "N" [x]]]
      [[pred "ADD" [x; zero; x]]]).

Definition benchmark_08 : judgment :=
  mk_judgment fo_definitions
    (mk_sequent
      [[tagged_pred 0 "N" [x]; tagged_pred 1 "N" [y];
        tagged_pred 2 "ADD" [x; y; z]]]
      [[pred "N" [z]]]).

Definition benchmark_09 : judgment :=
  mk_judgment fo_definitions
    (mk_sequent
      [[tagged_pred 0 "N" [x]; tagged_pred 1 "N" [y];
        tagged_pred 2 "ADD" [x; y; z]]]
      [[pred "ADD" [x; succ y; succ z]]]).

Definition benchmark_13 : judgment :=
  mk_judgment fo_definitions
    (mk_sequent [[tagged_pred 0 "N" [y]; tagged_pred 1 "N" [x]]]
      [[pred "H" [x; y]]]).

Definition benchmark_14 : judgment :=
  mk_judgment fo_definitions
    (mk_sequent [[tagged_pred 0 "N" [y]; tagged_pred 1 "N" [x]]]
      [[pred "N2" [x; y]]]).

Ltac finish_free_right :=
  match goal with
  | |- right_holds ?interp ?rho ?rhs =>
      apply (proj2 (right_holds_free interp rho rhs ltac:(reflexivity)))
  end.

Theorem benchmark_01_valid : Cyclic.Valid benchmark_01.
Proof.
  intros [i rho]. unfold benchmark_01, denote, sequent_holds; simpl.
  intros Hmodel [p [[Hp_eq | []] Hp]]. subst p. simpl in Hp.
  finish_free_right. exists [pred "N" [x]]. split; [now left|].
  simpl. split; [|exact I]. now apply odd_natural.
Qed.

Theorem benchmark_02_valid : Cyclic.Valid benchmark_02.
Proof.
  intros [i rho]. unfold benchmark_02, denote, sequent_holds; simpl.
  intros Hmodel [p [[Hp_eq | [Hp_eq | []]] Hp]].
  - subst p. simpl in Hp. finish_free_right.
    exists [pred "N" [x]]. split; [now left|]. simpl. split; [|exact I].
    now apply even_natural.
  - subst p. simpl in Hp. finish_free_right.
    exists [pred "N" [x]]. split; [now left|]. simpl. split; [|exact I].
    now apply odd_natural.
Qed.

Theorem benchmark_04_valid : Cyclic.Valid benchmark_04.
Proof.
  intros [i rho]. unfold benchmark_04, denote, sequent_holds; simpl.
  intros Hmodel [p [[Hp_eq | []] Hp]]. subst p. simpl in Hp.
  destruct (natural_parity i (rho (free_var 0)) Hmodel (proj1 Hp)) as [Ho | He].
  - finish_free_right. exists [pred "O" [x]]. split; [now left|].
    simpl. auto.
  - finish_free_right. exists [pred "E" [x]]. split; [right; now left|].
    simpl. auto.
Qed.

Theorem benchmark_05_valid : Cyclic.Valid benchmark_05.
Proof.
  intros [i rho]. unfold benchmark_05, denote, sequent_holds; simpl.
  intros Hmodel [p [[Hp_eq | []] Hp]]. subst p.
  simpl in Hp. destruct Hp as [Hnx [Hny _]].
  finish_free_right. exists [pred "Q" [x; y]]. split; [now left|].
  simpl. split; [|exact I]. now apply q_for_naturals.
Qed.

Theorem benchmark_07_valid : Cyclic.Valid benchmark_07.
Proof.
  intros [i rho]. unfold benchmark_07, denote, sequent_holds; simpl.
  intros Hmodel [p [[Hp_eq | []] Hp]]. subst p. simpl in Hp.
  finish_free_right. exists [pred "ADD" [x; zero; x]]. split; [now left|].
  simpl. split; [|exact I]. now apply add_zero_right.
Qed.

Theorem benchmark_08_valid : Cyclic.Valid benchmark_08.
Proof.
  intros [i rho]. unfold benchmark_08, denote, sequent_holds; simpl.
  intros Hmodel [p [[Hp_eq | []] Hp]]. subst p.
  simpl in Hp. destruct Hp as [_ [_ [Hadd _]]].
  finish_free_right. exists [pred "N" [z]]. split; [now left|].
  simpl. split; [|exact I]. eapply add_result_natural; eauto.
Qed.

Theorem benchmark_09_valid : Cyclic.Valid benchmark_09.
Proof.
  intros [i rho]. unfold benchmark_09, denote, sequent_holds; simpl.
  intros Hmodel [p [[Hp_eq | []] Hp]]. subst p.
  simpl in Hp. destruct Hp as [_ [_ [Hadd _]]].
  finish_free_right. exists [pred "ADD" [x; succ y; succ z]].
  split; [now left|]. simpl. split; [|exact I]. now apply add_shift_right.
Qed.

Theorem benchmark_13_valid : Cyclic.Valid benchmark_13.
Proof.
  intros [i rho]. unfold benchmark_13, denote, sequent_holds; simpl.
  intros Hmodel [p [[Hp_eq | []] Hp]]. subst p.
  simpl in Hp. destruct Hp as [Hny [Hnx _]].
  finish_free_right. exists [pred "H" [x; y]]. split; [now left|].
  simpl. split; [|exact I]. now apply h_for_naturals.
Qed.

Theorem benchmark_14_valid : Cyclic.Valid benchmark_14.
Proof.
  intros [i rho]. unfold benchmark_14, denote, sequent_holds; simpl.
  intros Hmodel [p [[Hp_eq | []] Hp]]. subst p.
  simpl in Hp. destruct Hp as [Hny [Hnx _]].
  finish_free_right. exists [pred "N2" [x; y]]. split; [now left|].
  simpl. split; [|exact I]. now apply n2_for_naturals.
Qed.

Inductive positive_benchmark : Type :=
| B01 | B02 | B04 | B05 | B07 | B08 | B09 | B13 | B14.

Definition benchmark_judgment (b : positive_benchmark) : judgment :=
  match b with
  | B01 => benchmark_01 | B02 => benchmark_02 | B04 => benchmark_04
  | B05 => benchmark_05 | B07 => benchmark_07 | B08 => benchmark_08
  | B09 => benchmark_09 | B13 => benchmark_13 | B14 => benchmark_14
  end.

(** The benchmark dispatcher is proof-producing: selecting an input returns
    an axiom payload whose theorem field is checked by the Rocq kernel. *)
Definition prove_positive_benchmark (b : positive_benchmark)
  : Cyclic.axiom_instance :=
  match b as b' return Cyclic.axiom_instance with
  | B01 => {| Cyclic.axiom_name := "verified-search/01";
              Cyclic.axiom_conclusion := benchmark_judgment B01;
              Cyclic.axiom_theorem := benchmark_01_valid |}
  | B02 => {| Cyclic.axiom_name := "verified-search/02";
              Cyclic.axiom_conclusion := benchmark_judgment B02;
              Cyclic.axiom_theorem := benchmark_02_valid |}
  | B04 => {| Cyclic.axiom_name := "verified-search/04";
              Cyclic.axiom_conclusion := benchmark_judgment B04;
              Cyclic.axiom_theorem := benchmark_04_valid |}
  | B05 => {| Cyclic.axiom_name := "verified-search/05";
              Cyclic.axiom_conclusion := benchmark_judgment B05;
              Cyclic.axiom_theorem := benchmark_05_valid |}
  | B07 => {| Cyclic.axiom_name := "verified-search/07";
              Cyclic.axiom_conclusion := benchmark_judgment B07;
              Cyclic.axiom_theorem := benchmark_07_valid |}
  | B08 => {| Cyclic.axiom_name := "verified-search/08";
              Cyclic.axiom_conclusion := benchmark_judgment B08;
              Cyclic.axiom_theorem := benchmark_08_valid |}
  | B09 => {| Cyclic.axiom_name := "verified-search/09";
              Cyclic.axiom_conclusion := benchmark_judgment B09;
              Cyclic.axiom_theorem := benchmark_09_valid |}
  | B13 => {| Cyclic.axiom_name := "verified-search/13";
              Cyclic.axiom_conclusion := benchmark_judgment B13;
              Cyclic.axiom_theorem := benchmark_13_valid |}
  | B14 => {| Cyclic.axiom_name := "verified-search/14";
              Cyclic.axiom_conclusion := benchmark_judgment B14;
              Cyclic.axiom_theorem := benchmark_14_valid |}
  end.

Example all_positive_benchmarks_dispatched :
  map (fun b => judgment_eqb (prove_positive_benchmark b).(Cyclic.axiom_conclusion)
                   (benchmark_judgment b))
    [B01; B02; B04; B05; B07; B08; B09; B13; B14] =
  repeat true 9.
Proof. vm_compute. reflexivity. Qed.
