From Stdlib Require Import List String.
From CyclistRocq.FirstOrderNew Require Export Definitions.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Definition x := Var (Free 0).
Definition y := Var (Free 1).
Definition z := Var (Free 2).
Definition w := Var (Free 3).
Definition ip p ts := Pred 0 p ts.
Definition mk_clause p ts atoms := {| clause_name := p; head := ts; body := atoms |}.
Definition natural_definitions := [
  mk_clause "N" [zero] [];
  mk_clause "N" [successor x] [ip "N" [x]]].
Definition n2_definitions := [
  mk_clause "N2" [zero;y] [ip "N" [y]];
  mk_clause "N2" [successor x;y] [ip "N2" [y;x]]].
Definition parity_definitions := [
  mk_clause "E" [zero] [];
  mk_clause "E" [successor x] [ip "O" [x]];
  mk_clause "O" [successor x] [ip "E" [x]]].
Definition pq_definitions := [
  mk_clause "P" [zero] [];
  mk_clause "P" [successor x] [ip "P" [x];ip "Q" [x;successor x]];
  mk_clause "Q" [x;zero] [];
  mk_clause "Q" [x;successor y] [ip "Q" [x;y];ip "P" [x]]].
Definition list_definitions := [
  mk_clause "LIST" [zero] [];
  mk_clause "LIST" [cons y x] [ip "LIST" [x]];
  mk_clause "APP" [zero;x;x] [];
  mk_clause "APP" [cons w x;y;cons w z] [ip "APP" [x;y;z]];
  mk_clause "TAKE" [x;zero;zero] [];
  mk_clause "TAKE" [zero;x;zero] [];
  mk_clause "TAKE" [successor x;cons w y;cons w z] [ip "TAKE" [x;y;z]];
  mk_clause "DROP" [x;zero;zero] [];
  mk_clause "DROP" [zero;x;x] [];
  mk_clause "DROP" [successor x;cons w y;z] [ip "DROP" [x;y;z]];
  mk_clause "MINUS" [zero;x;zero] [];
  mk_clause "MINUS" [x;zero;x] [];
  mk_clause "MINUS" [successor x;successor y;z] [ip "MINUS" [x;y;z]];
  mk_clause "LEN" [zero;zero] [];
  mk_clause "LEN" [cons z x;successor y] [ip "LEN" [x;y]]].
Definition plus_definitions := [
  mk_clause "PLUS" [zero;x;x] [];
  mk_clause "PLUS" [successor x;y;successor z] [ip "PLUS" [x;y;z]]].
Definition count_definitions := [
  mk_clause "COUNT" [x;zero;zero] [];
  mk_clause "COUNT" [x;cons x y;successor z] [ip "COUNT" [x;y;z]];
  mk_clause "COUNT" [x;cons w y;z] [Deq x w;ip "COUNT" [x;y;z]]].
Definition add_definitions := [
  mk_clause "ADD" [zero;x;x] [ip "N" [x]];
  mk_clause "ADD" [successor x;y;successor z] [ip "ADD" [x;y;z]]].
Definition mul_definitions := [
  mk_clause "MUL" [zero;x;zero] [ip "N" [x]];
  mk_clause "MUL" [successor x;y;w] [ip "MUL" [x;y;z];ip "ADD_2" [x;z;w]]].
Definition leq_definitions := [
  mk_clause "LEQ" [zero;x] [];
  mk_clause "LEQ" [successor x;successor y] [ip "LEQ" [x;y]]].
Definition r_definitions := [
  mk_clause "R" [zero;x] [];
  mk_clause "R" [successor x;zero] [ip "R" [x;zero]];
  mk_clause "R" [successor x;successor y] [ip "R" [successor (successor x);y]]].
Definition hydra_definitions := [
  mk_clause "H" [zero;zero] [];
  mk_clause "H" [successor zero;zero] [];
  mk_clause "H" [x;successor zero] [];
  mk_clause "H" [successor x;successor (successor y)] [ip "H" [x;y]];
  mk_clause "H" [zero;successor (successor y)] [ip "H" [successor y;y]];
  mk_clause "H" [successor (successor x);zero] [ip "H" [successor x;x]]].

(** Closed part of the supplied library; no reference is silently repaired. *)
Definition closed_source_definitions := natural_definitions ++ n2_definitions ++
  parity_definitions ++ pq_definitions ++ list_definitions ++ plus_definitions ++
  count_definitions ++ add_definitions ++ leq_definitions ++ r_definitions ++ hydra_definitions.
Definition source_definitions := natural_definitions ++ n2_definitions ++
  parity_definitions ++ pq_definitions ++ list_definitions ++ plus_definitions ++
  count_definitions ++ add_definitions ++ mul_definitions ++ leq_definitions ++
  r_definitions ++ hydra_definitions.
Example closed_source_is_well_formed : definitions_wfb closed_source_definitions = true.
Proof. vm_compute; reflexivity. Qed.
Example literal_source_reports_add_2 : definition_errors source_definitions = ["ADD_2"].
Proof. vm_compute; reflexivity. Qed.
Example count_guard_is_disequality :
  body (mk_clause "COUNT" [x;cons w y;z] [Deq x w;ip "COUNT" [x;y;z]])
  = [Deq x w;ip "COUNT" [x;y;z]].
Proof. reflexivity. Qed.
