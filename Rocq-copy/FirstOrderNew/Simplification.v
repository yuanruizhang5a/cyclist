From Stdlib Require Import List Bool Arith String.
From CyclistRocq.FirstOrderNew Require Export Rules.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Definition identity_trace j := {| continuations := map (fun t => (t,t)) (trace_tags j);
  progressing := [] |}.
Definition unary_application name j k edge := {| application_name := name;
  conclusion := j; premises := [{| premise_label := k; premise_trace := edge |}] |}.
Definition map_sequent f j := {| antecedent := map f j.(antecedent);
                               succedent := map f j.(succedent) |}.
Definition reflexive_eqb a := match a with Eq t u => term_eqb t u | _ => false end.
Definition without_trivial p := filter (fun a => negb (reflexive_eqb a)) p.
Definition eq_binding a := match a with
  | Eq t (Var v) => if term_eqb t (Var v) then None else Some (v,t)
  | Eq (Var v) t => if term_eqb (Var v) t then None else Some (v,t)
  | _ => None end.
Definition ex_binding a := match a with
  | Eq t (Var (Exist n)) => Some (Exist n,t)
  | Eq (Var (Exist n)) t => Some (Exist n,t)
  | _ => None end.
Fixpoint first_some {A B} (f : A -> option B) xs := match xs with
  | [] => None | x::xs' => match f x with Some y => Some y | None => first_some f xs' end end.
Definition constructor_eqs injective a := match a with
  | Eq (Fun f ts) (Fun g us) => if String.eqb f g && Nat.eqb (List.length ts) (List.length us)
      && (negb injective || String.eqb f "s" || String.eqb f "cons")
    then Some (map (fun tu => Eq (fst tu) (snd tu)) (combine ts us)) else None
  | _ => None end.
Fixpoint expand_first injective p := match p with
  | [] => None
  | a::p' => match constructor_eqs injective a with
    | Some eqs => Some (eqs++p')
    | None => match expand_first injective p' with
      | Some p'' => Some (a::p'') | None => None end end end.
Definition simplify_trivial j :=
  let k := map_sequent without_trivial j in
  if sequent_eqb j k then None else Some k.
Definition simplify_left_equality j := match j.(antecedent) with
  | [p] => match first_some eq_binding p with
    | Some (v,t) => Some (subst_sequent [(v,t)] j) | None => None end
  | _ => None end.
Definition simplify_right_equality j := first_some
  (fun p => match first_some ex_binding p with
    | Some (v,t) => Some {| antecedent := j.(antecedent);
      succedent := replace_product p (subst_product [(v,t)] p) j.(succedent) |}
    | None => None end) j.(succedent).
Definition simplify_right_atoms j := match j.(antecedent) with
  | [p] => let k := {| antecedent := [p]; succedent := map
      (fun q => filter (fun a => negb (logical_mem a p)) q) j.(succedent) |} in
    if sequent_eqb j k then None else Some k
  | _ => None end.
Definition simplify_left_injective j := first_some
  (fun p => match expand_first true p with
    | Some q => Some {| antecedent := replace_product p q j.(antecedent);
                       succedent := j.(succedent) |} | None => None end) j.(antecedent).
Definition simplify_right_congruence j := first_some
  (fun p => match expand_first false p with
    | Some q => Some {| antecedent := j.(antecedent);
                       succedent := replace_product p q j.(succedent) |} | None => None end) j.(succedent).
Definition simplify_once j := first_some (fun f => f j)
  [simplify_trivial; simplify_left_equality; simplify_right_equality;
   simplify_right_atoms; simplify_left_injective; simplify_right_congruence].
Inductive simplification_result := Normal (j : sequent) | Exhausted (j : sequent).
Fixpoint simplify fuel j := match fuel with
  | 0 => match simplify_once j with None => Normal j | Some _ => Exhausted j end
  | S fuel' => match simplify_once j with None => Normal j | Some k => simplify fuel' k end end.

Example cyclic_equality_terminates_with_exhaustion :
  match simplify 5 {| antecedent := [[Eq (Var (Free 0)) (successor (Var (Free 0)))]];
    succedent := [] |} with Exhausted _ => true | Normal _ => false end = true.
Proof. reflexivity. Qed.
