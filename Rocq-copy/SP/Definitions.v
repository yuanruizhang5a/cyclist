From Stdlib Require Import List String.

From CyclistRocq.SP Require Import Syntax.

Import ListNotations.
Open Scope string_scope.

(** * Reified separation-logic definition libraries

    The following tables are direct syntax trees, not parser output.  Within
    each predicate, [F 0], [F 1], ... are formal parameters and [E n] are
    clause-local variables corresponding to primed names in the source files. *)
Definition F n : term := Var (free_var n).
Definition E n : term := Var (existential_var n).
Definition EQ x y := Equal x y.
Definition NEQ x y := Disequal x y.
Definition PTO x fields := pto x fields.
Definition PR name args := untagged_pred name args.
Definition SH pure points predicates := mk_heap pure points predicates.
Definition CL body head := mk_clause body head.

Definition rlist_clauses : list clause :=
  [CL (SH [] [PTO (F 0) [F 1]] []) [F 0; F 1];
   CL (SH [] [PTO (E 0) [F 1]] [PR "RList" [F 0; E 0]]) [F 0; F 1]].

Definition evenlist_clauses : list clause :=
  [CL (SH [EQ (F 0) (F 1)] [] []) [F 0; F 1];
   CL (SH [NEQ (F 0) (F 1)]
     [PTO (F 0) [E 0]; PTO (E 0) [E 1]]
     [PR "EvenList" [E 1; F 1]]) [F 0; F 1]].

Definition list_cap_clauses : list clause :=
  [CL (SH [] [PTO (F 0) [F 1]] []) [F 0; F 1];
   CL (SH [] [PTO (F 0) [E 0]] [PR "List" [E 0; F 1]]) [F 0; F 1]].

Definition listo_clauses : list clause :=
  [CL (SH [] [PTO (F 0) [F 1]] []) [F 0; F 1];
   CL (SH [] [PTO (F 0) [E 0]] [PR "ListE" [E 0; F 1]]) [F 0; F 1]].

Definition liste_clauses : list clause :=
  [CL (SH [] [PTO (F 0) [E 0]] [PR "ListO" [E 0; F 1]]) [F 0; F 1]].

Definition pelist_clauses : list clause :=
  [CL (SH [EQ (F 0) (F 1)] [] []) [F 0; F 1];
   CL (SH [] [PTO (F 0) [E 0]] [PR "PeList" [E 0; F 1]]) [F 0; F 1]].

Definition dll_clauses : list clause :=
  [CL (SH [EQ (F 0) (F 1); EQ (F 2) (F 3)] [] []) [F 0; F 1; F 2; F 3];
   CL (SH [] [PTO (F 0) [E 0; F 3]]
     [PR "DLL" [E 0; F 1; F 2; F 0]]) [F 0; F 1; F 2; F 3]].

Definition sll_clauses : list clause :=
  [CL (SH [EQ (F 0) (F 1)] [] []) [F 0; F 1];
   CL (SH [] [PTO (F 0) [E 0; E 1]] [PR "SLL" [E 0; F 1]]) [F 0; F 1]].

Definition bsll_clauses : list clause :=
  [CL (SH [EQ (F 0) (F 1)] [] []) [F 0; F 1];
   CL (SH [] [PTO (E 0) [E 1; F 1]] [PR "BSLL" [F 0; E 0]]) [F 0; F 1]].

Definition funqueue_clauses : list clause :=
  [CL (SH []
     [PTO (F 0) [E 0; E 1]; PTO (E 0) [E 2; E 3]]
     [PR "SLL" [E 1; Nil]; PR "SLL" [E 3; Nil]]) [F 0]].

Definition emptyfunqueue_clauses : list clause :=
  [CL (SH [] [PTO (F 0) [E 0; Nil]; PTO (E 0) [E 1; Nil]] []) [F 0]].

Definition funqueuelists_clauses : list clause :=
  [CL (SH [EQ (F 0) Nil; EQ (F 1) Nil] [] []) [F 0; F 1];
   CL (SH [EQ (F 0) Nil] [PTO (F 1) [E 0; E 1]]
     [PR "funQueueLists" [F 0; E 0]]) [F 0; F 1];
   CL (SH [] [PTO (F 0) [E 0; E 1]]
     [PR "funQueueLists" [E 0; F 1]]) [F 0; F 1]].

Definition funqueue_small_clauses : list clause :=
  [CL (SH [] [PTO (F 0) [E 0; F 1]; PTO (E 0) [E 1; F 2]]
     [PR "funQueueLists" [F 1; F 2]]) [F 0; F 1; F 2]].

Definition bintree_clauses : list clause :=
  [CL emp [F 0];
   CL (SH [] [PTO (F 0) [E 0; E 1]]
     [PR "BinTree" [E 0]; PR "BinTree" [E 1]]) [F 0]].

Definition bintreeseg_clauses : list clause :=
  [CL (SH [EQ (F 0) (F 1)] [] []) [F 0; F 1];
   CL (SH [] [PTO (F 0) [E 0; E 1]]
     [PR "BinTreeSeg" [E 0; F 1]; PR "BinTree" [E 1]]) [F 0; F 1];
   CL (SH [] [PTO (F 0) [E 0; E 1]]
     [PR "BinTree" [E 0]; PR "BinTreeSeg" [E 1; F 1]]) [F 0; F 1]].

Definition binlistfirst_clauses : list clause :=
  [CL emp [F 0];
   CL (SH [] [PTO (F 0) [E 0; E 1]] [PR "BinListFirst" [E 0]]) [F 0]].

Definition binlistsecond_clauses : list clause :=
  [CL emp [F 0];
   CL (SH [] [PTO (F 0) [E 0; E 1]] [PR "BinListSecond" [E 1]]) [F 0]].

Definition binpath_clauses : list clause :=
  [CL (SH [EQ (F 0) (F 1)] [] []) [F 0; F 1];
   CL (SH [] [PTO (F 0) [E 0; E 1]] [PR "BinPath" [E 0; F 1]]) [F 0; F 1];
   CL (SH [] [PTO (F 0) [E 0; E 1]] [PR "BinPath" [E 1; F 1]]) [F 0; F 1]].

Definition ls_clauses : list clause :=
  [CL (SH [EQ (F 0) (F 1)] [] []) [F 0; F 1];
   CL (SH [NEQ (F 0) (F 1)] [PTO (F 0) [E 0]]
     [PR "ls" [E 0; F 1]]) [F 0; F 1]].

Definition ls2_clauses : list clause :=
  [CL (SH [EQ (F 0) (F 1)] [] []) [F 0; F 1];
   CL (SH [NEQ (F 0) (F 1)] [PTO (F 0) [E 0; E 1]]
     [PR "ls2" [E 0; F 1]]) [F 0; F 1]].

Definition list_lower_clauses : list clause :=
  [CL (SH [EQ (F 0) Nil] [] []) [F 0];
   CL (SH [] [PTO (F 0) [E 0]] [PR "list" [E 0]]) [F 0]].

Definition rls_clauses : list clause :=
  [CL (SH [EQ (F 0) (F 1)] [] []) [F 0; F 1];
   CL (SH [NEQ (F 0) (F 1)] [PTO (E 0) [F 1]]
     [PR "rls" [F 0; E 0]]) [F 0; F 1]].

Definition bt_clauses : list clause :=
  [CL (SH [EQ (F 0) Nil] [] []) [F 0];
   CL (SH [] [PTO (F 0) [E 0; E 1]] [PR "bt" [E 0]; PR "bt" [E 1]]) [F 0]].

Definition btseg_clauses : list clause :=
  [CL (SH [EQ (F 0) (F 1)] [] []) [F 0; F 1];
   CL (SH [] [PTO (F 0) [E 0; E 1]]
     [PR "bt" [E 0]; PR "btseg" [E 1; F 1]]) [F 0; F 1];
   CL (SH [] [PTO (F 0) [E 0; E 1]]
     [PR "btseg" [E 0; F 1]; PR "bt" [E 1]]) [F 0; F 1]].

Definition cls_clauses : list clause :=
  [CL (SH [] [PTO (F 0) [E 0]] [PR "ls" [E 0; F 0]]) [F 0]].

Definition dls_clauses : list clause :=
  [CL (SH [EQ (F 0) (F 1)] [] []) [F 0; F 1];
   CL (SH [NEQ (F 0) (F 1)] [PTO (F 0) [E 0; E 1]]
     [PR "dls" [E 1; F 1]]) [F 0; F 1]].

Definition lsls_clauses : list clause :=
  [CL (SH [EQ (F 0) Nil] [] []) [F 0];
   CL (SH [] [PTO (F 0) [E 0; E 1]]
     [PR "lsls" [E 0]; PR "dls" [E 1; Nil]]) [F 0]].

Definition lsbt_clauses : list clause :=
  [CL (SH [EQ (F 0) Nil] [] []) [F 0];
   CL (SH [] [PTO (F 0) [E 0; E 1]]
     [PR "lsbt" [E 1]; PR "bt" [E 0]]) [F 0]].

Definition emptyqueue_clauses : list clause :=
  [CL (SH [] [PTO (F 0) [Nil; Nil]] []) [F 0]].

Definition queue_clauses : list clause :=
  [CL (SH [] [PTO (F 0) [Nil; Nil]] []) [F 0];
   CL (SH [] [PTO (F 0) [E 0; E 1]; PTO (E 1) [Nil; Nil]]
     [PR "ls2" [E 0; E 1]]) [F 0]].

Definition uf_clauses : list clause :=
  [CL (SH [EQ (E 0) (F 1)] [PTO (E 0) [F 1]]
     [PR "ls" [F 0; E 0]]) [F 0; F 1]].

Definition ls_set_clauses : list clause :=
  [CL emp [F 0];
   CL (SH [NEQ (E 0) Nil] []
     [PR "ls" [E 0; F 0]; PR "ls_set" [F 0]]) [F 0]].

Definition tree_clauses : list clause :=
  [CL (SH [EQ (F 0) Nil] [] []) [F 0];
   CL (SH [] [PTO (F 0) [E 0; E 1]] [PR "treels" [E 1; Nil]]) [F 0]].

Definition treels_clauses : list clause :=
  [CL (SH [EQ (F 0) (F 1)] [] []) [F 0; F 1];
   CL (SH [NEQ (F 0) (F 1)] [PTO (F 0) [E 0; E 1]]
     [PR "treels" [E 0; F 1]; PR "tree" [E 1]]) [F 0; F 1]].

Definition duptree_clauses : list clause :=
  [CL (SH [EQ (F 0) Nil] [] []) [F 0];
   CL (SH [] [PTO (F 0) [E 0; E 1]] [PR "duptreels" [E 1; Nil]]) [F 0]].

Definition duptreels_clauses : list clause :=
  [CL (SH [EQ (F 0) (F 1)] [] []) [F 0; F 1];
   CL (SH [NEQ (F 0) (F 1)]
     [PTO (F 0) [E 0; E 1]; PTO (E 0) [E 2; E 1]]
     [PR "duptreels" [E 2; F 1]; PR "duptree" [E 1]]) [F 0; F 1]].

Definition sptrue_clauses : list clause :=
  [CL emp [];
   CL (SH [] [PTO (E 0) [E 1]] [PR "spTrue" []]) []].

Definition sptrue2_clauses : list clause :=
  [CL emp [];
   CL (SH [] [PTO (E 0) [E 1; E 2]] [PR "spTrue2" []]) []].

(** Every definition from [examples/sl.defs], in source order. *)
Definition sl_definitions : definitions :=
  [("RList", rlist_clauses);
   ("EvenList", evenlist_clauses);
   ("List", list_cap_clauses);
   ("ListO", listo_clauses);
   ("ListE", liste_clauses);
   ("PeList", pelist_clauses);
   ("DLL", dll_clauses);
   ("SLL", sll_clauses);
   ("BSLL", bsll_clauses);
   ("FunQueue", funqueue_clauses);
   ("EmptyFunQueue", emptyfunqueue_clauses);
   ("funQueueLists", funqueuelists_clauses);
   ("funQueue", funqueue_small_clauses);
   ("BinTree", bintree_clauses);
   ("BinTreeSeg", bintreeseg_clauses);
   ("BinListFirst", binlistfirst_clauses);
   ("BinListSecond", binlistsecond_clauses);
   ("BinPath", binpath_clauses);
   ("ls", ls_clauses);
   ("ls2", ls2_clauses);
   ("list", list_lower_clauses);
   ("rls", rls_clauses);
   ("bt", bt_clauses);
   ("btseg", btseg_clauses);
   ("cls", cls_clauses);
   ("dls", dls_clauses);
   ("lsls", lsls_clauses);
   ("lsbt", lsbt_clauses);
   ("EmptyQueue", emptyqueue_clauses);
   ("Queue", queue_clauses);
   ("uf", uf_clauses);
   ("ls_set", ls_set_clauses);
   ("tree", tree_clauses);
   ("treels", treels_clauses);
   ("duptree", duptree_clauses);
   ("duptreels", duptreels_clauses);
   ("spTrue", sptrue_clauses);
   ("spTrue2", sptrue2_clauses)].

(** Dependency closure needed by ATVA-2014/01. *)
Definition atva_dll_clauses : list clause :=
  [CL (SH [EQ (F 0) (F 2)] [PTO (F 0) [F 3; F 1]] []) [F 0; F 1; F 2; F 3];
   CL (SH [] [PTO (F 0) [E 0; F 1]]
     [PR "DLL" [E 0; F 0; F 2; F 3]]) [F 0; F 1; F 2; F 3]].

Definition atva_dll_rev_clauses : list clause :=
  [CL (SH [EQ (F 0) (F 2)] [PTO (F 0) [F 3; F 1]] []) [F 0; F 1; F 2; F 3];
   CL (SH [] [PTO (F 2) [F 3; E 0]]
     [PR "DLL_rev" [F 0; F 1; E 0; F 2]]) [F 0; F 1; F 2; F 3]].

Definition atva_definitions : definitions :=
  [("DLL", atva_dll_clauses); ("DLL_rev", atva_dll_rev_clauses)].

(** Dependency closure needed by the two selected Songbird inputs. *)
Definition songbird_ls_clauses : list clause :=
  [CL (SH [EQ (F 0) (F 1)] [] []) [F 0; F 1];
   CL (SH [] [PTO (F 0) [E 0]] [PR "ls" [E 0; F 1]]) [F 0; F 1]].

Definition songbird_ls2_clauses : list clause :=
  [CL (SH [EQ (F 0) (F 1)] [] []) [F 0; F 1];
   CL (SH [] [PTO (F 0) [E 0]] [PR "ls2" [E 0; F 1]]) [F 0; F 1];
   CL (SH [] [PTO (F 0) [E 0]; PTO (E 0) [E 1]]
     [PR "ls2" [E 1; F 1]]) [F 0; F 1]].

Definition songbird_even_clauses : list clause :=
  [CL (SH [EQ (F 0) (F 1)] [] []) [F 0; F 1];
   CL (SH [] [PTO (F 0) [E 0]] [PR "ls_odd" [E 0; F 1]]) [F 0; F 1]].

Definition songbird_odd_clauses : list clause :=
  [CL (SH [] [PTO (F 0) [F 1]] []) [F 0; F 1];
   CL (SH [] [PTO (F 0) [E 0]] [PR "ls_even" [E 0; F 1]]) [F 0; F 1]].

Definition songbird_all2_clauses : list clause :=
  [CL (SH [] [] [PR "ls_even" [F 0; F 1]]) [F 0; F 1];
   CL (SH [] [] [PR "ls_odd" [F 0; F 1]]) [F 0; F 1]].

Definition songbird_definitions : definitions :=
  [("ls", songbird_ls_clauses);
   ("ls2", songbird_ls2_clauses);
   ("ls_even", songbird_even_clauses);
   ("ls_odd", songbird_odd_clauses);
   ("ls_all2", songbird_all2_clauses)].

Example all_sl_definitions_reified : List.length sl_definitions = 38.
Proof. reflexivity. Qed.
