From Stdlib Require Import List Bool Arith ZArith String.
From CyclistRocq.FirstOrderNew Require Export Definitions.
Import ListNotations.

Fixpoint binding s x : option term := match s with
  | [] => None | (y,t)::s' => if variable_eqb x y then Some t else binding s' x end.
Definition extend_binding s x t :=
  match binding s x with
  | Some u => if term_eqb u t then Some s else None
  | None => match x with
    | Free _ => Some ((x,t)::s)
    | Exist _ => match t with
      | Var (Exist _) => if existsb (fun xt => term_eqb (snd xt) t) s
                         then None else Some ((x,t)::s)
      | _ => None end end end.
Fixpoint raw_match (fuel : nat) s t u : option substitution :=
  match fuel with 0 => None | S fuel' =>
    match t,u with
    | Var x,_ => extend_binding s x u
    | Const x,Const y => if Z.eqb x y then Some s else None
    | Fun f ts,Fun g us => if String.eqb f g then
      (fix args (xs ys : list term) (theta : substitution) :=
        match xs,ys with
        | [],[] => Some theta
        | x::xs',y::ys' => match raw_match fuel' theta x y with
            Some theta' => args xs' ys' theta' | None => None end
        | _,_ => None end) ts us s
      else None
    | _,_ => None end end.
Definition match_term fuel s t u :=
  match raw_match fuel s t u with
  | Some theta => if term_eqb (subst_term theta t) u then Some theta else None
  | None => None end.
Lemma match_term_correct fuel s t u theta :
  match_term fuel s t u = Some theta -> subst_term theta t = u.
Proof.
  unfold match_term. destruct (raw_match fuel s t u) as [s'|]; [|discriminate].
  destruct (term_eqb (subst_term s' t) u) eqn:E; [|discriminate].
  intro H; inversion H; subst. apply eqb_of_dec_spec in E; exact E.
Qed.
Fixpoint match_terms fuel s ts us := match ts,us with
  | [],[] => Some s
  | t::ts',u::us' => match match_term fuel s t u with
    | Some s' => match_terms fuel s' ts' us' | None => None end
  | _,_ => None end.
Definition match_atom fuel s a b := match a,b with
  | Pred _ p ts,Pred _ q us => if String.eqb p q then match_terms fuel s ts us else None
  | Eq t u,Eq v w | Deq t u,Deq v w =>
      match match_terms fuel s [t;u] [v;w] with
      | Some s' => Some s' | None => match_terms fuel s [t;u] [w;v] end
  | _,_ => None end.
Fixpoint match_product fuel s p q : list substitution := match p with
  | [] => [s]
  | a::p' => flat_map (fun b => match match_atom fuel s a b with
    | Some s' => match_product fuel s' p' q | None => [] end) q end.
Definition tagged_subset tags p q := forallb
  (fun a => match atom_tag a with
    | Some tag => if existsb (Nat.eqb tag) tags then mem_atom a q else logical_mem a q
    | None => mem_atom a q end) p.

(** Repeated-head matching is separate from directional matching. Each repeated
    variable contributes equalities; existential head variables are not rigid. *)
Fixpoint head_match fuel s t u : option (substitution * product) :=
  match fuel with 0 => None | S fuel' => match t,u with
  | Var x,_ => match binding s x with
    | None => Some ((x,u)::s,[])
    | Some v => Some (s,[Eq v u]) end
  | Const x,Const y => if Z.eqb x y then Some (s,[]) else None
  | Fun f ts,Fun g us => if String.eqb f g then
    (fix args xs ys theta := match xs,ys with
      | [],[] => Some (theta,[])
      | x::xs',y::ys' => match head_match fuel' theta x y with
        | Some (theta',eqs) => match args xs' ys' theta' with
          | Some (theta'',eqs') => Some (theta'',eqs++eqs') | None => None end
        | None => None end | _,_ => None end) ts us s else None
  | _,_ => None end end.
Fixpoint head_match_terms fuel s ts us := match ts,us with
  | [],[] => Some (s,[])
  | t::ts',u::us' => match head_match fuel s t u with
    | Some (s',eqs) => match head_match_terms fuel s' ts' us' with
      | Some (s'',eqs') => Some (s'',eqs++eqs') | None => None end
    | None => None end
  | _,_ => None end.
Example repeated_head_generates_constraint :
  head_match_terms 5 [] [Var (Free 0);Var (Free 0)] [zero;successor zero]
  = Some ([(Free 0,zero)],[Eq zero (successor zero)]).
Proof. reflexivity. Qed.
