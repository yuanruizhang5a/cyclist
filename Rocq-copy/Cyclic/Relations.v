From Stdlib Require Import List Bool Arith Lia.

Import ListNotations.

(** A small, executable implementation of Cyclist's two-point slope algebra.
    [Decrease] dominates [Stay] when two paths yield the same tag pair. *)
Inductive slope : Type := Stay | Decrease.

Definition slope_eqb (x y : slope) : bool :=
  match x, y with
  | Stay, Stay | Decrease, Decrease => true
  | _, _ => false
  end.

Definition slope_join (x y : slope) : slope :=
  match x, y with
  | Decrease, _ | _, Decrease => Decrease
  | _, _ => Stay
  end.

Definition slope_compose := slope_join.

Record arc : Type := {
  arc_source : nat;
  arc_target : nat;
  arc_slope : slope
}.

Definition arc_key_eqb (x y : arc) : bool :=
  Nat.eqb x.(arc_source) y.(arc_source) &&
  Nat.eqb x.(arc_target) y.(arc_target).

Fixpoint slope_at (r : list arc) (a b : nat) : option slope :=
  match r with
  | [] => None
  | x :: xs =>
      if Nat.eqb a x.(arc_source) && Nat.eqb b x.(arc_target)
      then Some x.(arc_slope)
      else slope_at xs a b
  end.

Fixpoint put_arc (x : arc) (r : list arc) : list arc :=
  match r with
  | [] => [x]
  | y :: ys =>
      if arc_key_eqb x y then
        {| arc_source := y.(arc_source);
           arc_target := y.(arc_target);
           arc_slope := slope_join x.(arc_slope) y.(arc_slope) |} :: ys
      else y :: put_arc x ys
  end.

Definition relation_union (r s : list arc) : list arc :=
  fold_left (fun acc x => put_arc x acc) s r.

Definition compose_from (x : arc) (s : list arc) : list arc :=
  fold_left
    (fun acc y =>
       if Nat.eqb x.(arc_target) y.(arc_source) then
         put_arc
           {| arc_source := x.(arc_source);
              arc_target := y.(arc_target);
              arc_slope := slope_compose x.(arc_slope) y.(arc_slope) |}
           acc
       else acc)
    s [].

Definition relation_compose (r s : list arc) : list arc :=
  fold_left
    (fun acc x => relation_union (compose_from x s) acc)
    r [].

Definition option_slope_eqb (x y : option slope) : bool :=
  match x, y with
  | None, None => true
  | Some a, Some b => slope_eqb a b
  | _, _ => false
  end.

Definition relation_eqb (r s : list arc) : bool :=
  forallb
    (fun x => option_slope_eqb
                (slope_at r x.(arc_source) x.(arc_target))
                (slope_at s x.(arc_source) x.(arc_target)))
    (r ++ s).

Definition relation_close_once (r : list arc) : list arc :=
  relation_union (relation_compose r r) r.

Fixpoint relation_closure (fuel : nat) (r : list arc) : list arc :=
  match fuel with
  | 0 => r
  | S fuel' =>
      let r' := relation_close_once r in
      if relation_eqb r r' then r else relation_closure fuel' r'
  end.

Definition has_decreasing_diagonal (r : list arc) : bool :=
  existsb
    (fun x =>
       match x.(arc_slope) with
       | Stay => false
       | Decrease => Nat.eqb x.(arc_source) x.(arc_target)
       end)
    r.

Record path_relation : Type := {
  path_source : nat;
  path_target : nat;
  path_arcs : list arc
}.

Definition path_relation_eqb (p q : path_relation) : bool :=
  Nat.eqb p.(path_source) q.(path_source) &&
  Nat.eqb p.(path_target) q.(path_target) &&
  relation_eqb p.(path_arcs) q.(path_arcs).

Fixpoint path_mem (p : path_relation) (ps : list path_relation) : bool :=
  match ps with
  | [] => false
  | q :: qs => path_relation_eqb p q || path_mem p qs
  end.

Definition add_path (p : path_relation) (ps : list path_relation)
  : list path_relation :=
  if path_mem p ps then ps else p :: ps.

Definition compose_paths (p q : path_relation) : option path_relation :=
  if Nat.eqb p.(path_target) q.(path_source) then
    Some {| path_source := p.(path_source);
            path_target := q.(path_target);
            path_arcs := relation_compose p.(path_arcs) q.(path_arcs) |}
  else None.

Definition path_close_once (ps : list path_relation) : list path_relation :=
  fold_left
    (fun acc p =>
       fold_left
         (fun acc' q =>
            match compose_paths p q with
            | Some r => add_path r acc'
            | None => acc'
            end)
         ps acc)
    ps ps.

Definition path_set_eqb (ps qs : list path_relation) : bool :=
  forallb (fun p => path_mem p qs) ps &&
  forallb (fun q => path_mem q ps) qs.

Fixpoint path_closure (fuel : nat) (ps : list path_relation)
  : list path_relation :=
  match fuel with
  | 0 => ps
  | S fuel' =>
      let ps' := path_close_once ps in
      if path_set_eqb ps ps' then ps else path_closure fuel' ps'
  end.

Definition loop_relation_ok (tag_fuel : nat) (p : path_relation) : bool :=
  if Nat.eqb p.(path_source) p.(path_target) then
    has_decreasing_diagonal (relation_closure tag_fuel p.(path_arcs))
  else true.

Definition relational_trace_check
    (path_fuel tag_fuel : nat) (base : list path_relation) : bool :=
  forallb (loop_relation_ok tag_fuel) (path_closure path_fuel base).

(** Small executable regression checks for the algebra itself. *)
Example compose_progress_dominates :
  relation_compose
    [{| arc_source := 0; arc_target := 1; arc_slope := Stay |}]
    [{| arc_source := 1; arc_target := 0; arc_slope := Decrease |}]
  = [{| arc_source := 0; arc_target := 0; arc_slope := Decrease |}].
Proof. reflexivity. Qed.

Example decreasing_loop_is_accepted :
  relational_trace_check 4 4
    [{| path_source := 0; path_target := 0;
        path_arcs :=
          [{| arc_source := 3; arc_target := 3;
              arc_slope := Decrease |}] |}] = true.
Proof. reflexivity. Qed.

Example flat_loop_is_rejected :
  relational_trace_check 4 4
    [{| path_source := 0; path_target := 0;
        path_arcs :=
          [{| arc_source := 3; arc_target := 3;
              arc_slope := Stay |}] |}] = false.
Proof. reflexivity. Qed.

