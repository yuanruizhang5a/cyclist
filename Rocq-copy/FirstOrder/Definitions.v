From Stdlib Require Import List String.

From CyclistRocq.FirstOrder Require Import Syntax.

Import ListNotations.
Open Scope string_scope.

Definition fv (n : nat) : term := Var (free_var n).
Definition ev (n : nat) : term := Var (existential_var n).

Definition clause_of (body : product) (head : list term) : clause :=
  {| clause_body := body; clause_head := head |}.

(** A direct Rocq transcription of [examples/fo.defs].  Clause order is
    retained because the executable search layer explores it in file order. *)
Definition n_clauses : list clause :=
  [clause_of [] [zero];
   clause_of [pred "N" [fv 0]] [succ (fv 0)]].

Definition n2_clauses : list clause :=
  [clause_of [pred "N" [fv 0]] [zero; fv 0];
   clause_of [pred "N2" [fv 0; fv 1]] [succ (fv 1); fv 0]].

Definition e_clauses : list clause :=
  [clause_of [] [zero];
   clause_of [pred "O" [fv 0]] [succ (fv 0)]].

Definition o_clauses : list clause :=
  [clause_of [pred "E" [fv 0]] [succ (fv 0)]].

Definition p_clauses : list clause :=
  [clause_of [] [zero];
   clause_of [pred "P" [fv 0]; pred "Q" [fv 0; succ (fv 0)]]
     [succ (fv 0)]].

Definition q_clauses : list clause :=
  [clause_of [] [fv 0; zero];
   clause_of [pred "Q" [fv 0; fv 1]; pred "P" [fv 0]]
     [fv 0; succ (fv 1)]].

Definition list_clauses : list clause :=
  [clause_of [] [zero];
   clause_of [pred "LIST" [fv 0]] [cons (fv 1) (fv 0)]].

Definition app_clauses : list clause :=
  [clause_of [] [zero; fv 0; fv 0];
   clause_of [pred "APP" [fv 0; fv 1; fv 2]]
     [cons (fv 3) (fv 0); fv 1; cons (fv 3) (fv 2)]].

Definition take_clauses : list clause :=
  [clause_of [] [fv 0; zero; zero];
   clause_of [] [zero; fv 0; zero];
   clause_of [pred "TAKE" [fv 0; fv 1; fv 2]]
     [succ (fv 0); cons (fv 3) (fv 1); cons (fv 3) (fv 2)]].

Definition drop_clauses : list clause :=
  [clause_of [] [fv 0; zero; zero];
   clause_of [] [zero; fv 0; fv 0];
   clause_of [pred "DROP" [fv 0; fv 1; fv 2]]
     [succ (fv 0); cons (fv 3) (fv 1); fv 2]].

Definition minus_clauses : list clause :=
  [clause_of [] [zero; fv 0; zero];
   clause_of [] [fv 0; zero; fv 0];
   clause_of [pred "MINUS" [fv 0; fv 1; fv 2]]
     [succ (fv 0); succ (fv 1); fv 2]].

Definition len_clauses : list clause :=
  [clause_of [] [zero; zero];
   clause_of [pred "LEN" [fv 0; fv 1]]
     [cons (fv 2) (fv 0); succ (fv 1)]].

Definition plus_clauses : list clause :=
  [clause_of [] [zero; fv 0; fv 0];
   clause_of [pred "PLUS" [fv 0; fv 1; fv 2]]
     [succ (fv 0); fv 1; succ (fv 2)]].

Definition count_clauses : list clause :=
  [clause_of [] [fv 0; zero; zero];
   clause_of [pred "COUNT" [fv 0; fv 1; fv 2]]
     [fv 0; cons (fv 0) (fv 1); succ (fv 2)];
   clause_of [Neq (fv 0) (fv 3); pred "COUNT" [fv 0; fv 1; fv 2]]
     [fv 0; cons (fv 3) (fv 1); fv 2]].

Definition add_clauses : list clause :=
  [clause_of [pred "N" [fv 0]] [zero; fv 0; fv 0];
   clause_of [pred "ADD" [fv 0; fv 1; fv 2]]
     [succ (fv 0); fv 1; succ (fv 2)]].

Definition mul_clauses : list clause :=
  [clause_of [pred "N" [fv 0]] [zero; fv 0; zero];
   clause_of [pred "MUL" [fv 0; fv 1; fv 2];
               pred "ADD_2" [fv 0; fv 2; fv 3]]
     [succ (fv 0); fv 1; fv 3]].

Definition leq_clauses : list clause :=
  [clause_of [] [zero; fv 0];
   clause_of [pred "LEQ" [fv 0; fv 1]] [succ (fv 0); succ (fv 1)]].

Definition r_clauses : list clause :=
  [clause_of [] [zero; fv 0];
   clause_of [pred "R" [fv 0; zero]] [succ (fv 0); zero];
   clause_of [pred "R" [succ (succ (fv 0)); fv 1]]
     [succ (fv 0); succ (fv 1)]].

Definition h_clauses : list clause :=
  [clause_of [] [zero; zero];
   clause_of [] [succ zero; zero];
   clause_of [] [fv 0; succ zero];
   clause_of [pred "H" [fv 0; fv 1]] [succ (fv 0); succ (succ (fv 1))];
   clause_of [pred "H" [succ (fv 1); fv 1]] [zero; succ (succ (fv 1))];
   clause_of [pred "H" [succ (fv 0); fv 0]] [succ (succ (fv 0)); zero]].

Definition fo_definitions : definitions :=
  [("N", n_clauses);
   ("N2", n2_clauses);
   ("E", e_clauses);
   ("O", o_clauses);
   ("P", p_clauses);
   ("Q", q_clauses);
   ("LIST", list_clauses);
   ("APP", app_clauses);
   ("TAKE", take_clauses);
   ("DROP", drop_clauses);
   ("MINUS", minus_clauses);
   ("LEN", len_clauses);
   ("PLUS", plus_clauses);
   ("COUNT", count_clauses);
   ("ADD", add_clauses);
   ("MUL", mul_clauses);
   ("LEQ", leq_clauses);
   ("R", r_clauses);
   ("H", h_clauses)].

Example lookup_n : lookup_definition "N" fo_definitions = n_clauses.
Proof. reflexivity. Qed.

Example lookup_h : lookup_definition "H" fo_definitions = h_clauses.
Proof. reflexivity. Qed.
