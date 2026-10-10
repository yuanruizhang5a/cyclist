From Stdlib Require Import List String.

From CyclistRocq.SP Require Import Syntax Definitions.

Import ListNotations.
Open Scope string_scope.

(** * The nine selected original inputs, reified without a parser *)

Definition benchmark_base_01_1 : judgment :=
  mk_judgment sl_definitions
    (mk_sequent
      (singleton_formula
        (SH [] [PTO (F 0) [F 1]] [PR "RList" [F 1; F 2]]))
      (singleton_formula (SH [] [] [PR "RList" [F 0; F 2]]))).

Definition benchmark_base_01_2 : judgment :=
  mk_judgment sl_definitions
    (mk_sequent
      (singleton_formula
        (SH [] [PTO (F 0) [F 1]]
          [pred (FreeTag 0) "RList" [F 1; F 2]]))
      (mk_formula [lt_constraint (FreeTag 0) (ExistentialTag 0)]
        [SH [] [] [pred (ExistentialTag 0) "RList" [F 0; F 2]]])).

Definition benchmark_base_02_1 : judgment :=
  mk_judgment sl_definitions
    (mk_sequent
      (singleton_formula
        (SH [] [] [PR "RList" [F 0; F 1]; PR "RList" [F 1; F 2]]))
      (singleton_formula (SH [] [] [PR "RList" [F 0; F 2]]))).

Definition benchmark_base_07_1 : judgment :=
  mk_judgment sl_definitions
    (mk_sequent
      (singleton_formula (SH [] [] [PR "DLL" [F 0; F 1; F 2; F 3]]))
      (singleton_formula (SH [] [] [PR "SLL" [F 0; F 1]]))).

Definition benchmark_base_19_1 : judgment :=
  mk_judgment sl_definitions
    (mk_sequent
      (singleton_formula
        (SH [NEQ (F 0) (F 2)] [PTO (F 0) [F 1]]
          [PR "ls" [F 1; F 2]]))
      (singleton_formula (SH [] [] [PR "ls" [F 0; F 2]]))).

Definition benchmark_base_21_1 : judgment :=
  mk_judgment sl_definitions
    (mk_sequent
      (mk_formula []
        [SH [] [] [PR "ListE" [F 0; F 1]];
         SH [] [] [PR "ListO" [F 0; F 1]]])
      (singleton_formula (SH [] [] [PR "List" [F 0; F 1]]))).

Definition benchmark_atva_01_1 : judgment :=
  mk_judgment atva_definitions
    (mk_sequent
      (singleton_formula
        (SH [] [] [PR "DLL" [F 0; F 1; F 2; F 3]]))
      (singleton_formula
        (SH [] [] [PR "DLL_rev" [F 0; F 1; F 2; F 3]]))).

Definition benchmark_songbird_ls2_ls : judgment :=
  mk_judgment songbird_definitions
    (mk_sequent
      (singleton_formula (SH [] [] [PR "ls2" [F 0; F 1]]))
      (singleton_formula (SH [] [] [PR "ls" [F 0; F 1]]))).

Definition benchmark_songbird_lsevenodd : judgment :=
  mk_judgment songbird_definitions
    (mk_sequent
      (singleton_formula (SH [] [] [PR "ls_all2" [F 0; F 1]]))
      (singleton_formula (SH [] [] [PR "ls" [F 0; F 1]]))).

Definition selected_benchmarks : list judgment :=
  [benchmark_base_01_1;
   benchmark_base_01_2;
   benchmark_base_02_1;
   benchmark_base_07_1;
   benchmark_base_19_1;
   benchmark_base_21_1;
   benchmark_atva_01_1;
   benchmark_songbird_ls2_ls;
   benchmark_songbird_lsevenodd].

Example selected_benchmark_count : List.length selected_benchmarks = 9.
Proof. reflexivity. Qed.
