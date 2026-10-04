From Stdlib Require Import List Bool Arith String Lia.
From CyclistRocq.FirstOrderNew Require Export Syntax.
Import ListNotations.

Definition substitution := list (variable * term).
Fixpoint lookup (s : substitution) x :=
  match s with [] => Var x | (y,t)::s' =>
    if variable_eqb x y then t else lookup s' x end.
Fixpoint subst_term s t :=
  match t with Const _ => t | Var x => lookup s x
  | Fun f ts => Fun f (map (subst_term s) ts) end.
Definition subst_atom s a :=
  match a with Eq t u => Eq (subst_term s t) (subst_term s u)
  | Deq t u => Deq (subst_term s t) (subst_term s u)
  | Pred tag p ts => Pred tag p (map (subst_term s) ts) end.
Definition subst_product s p := map (subst_atom s) p.
Definition subst_formula s f := map (subst_product s) f.
Definition subst_sequent s j :=
  {| antecedent := subst_formula s j.(antecedent);
     succedent := subst_formula s j.(succedent) |}.
Definition substitution_identityb s := forallb
  (fun xt => term_eqb (Var (fst xt)) (snd xt)) s.
Definition substitution_freeb s := forallb
  (fun xt => is_free (fst xt) && forallb is_free (term_vars (snd xt))) s.

Fixpoint rename_variables start (xs : list variable) : substitution :=
  match xs with [] => [] | x :: xs' =>
    (x, Var (match x with Free _ => Free start | Exist _ => Exist start end))
    :: rename_variables (S start) xs' end.
Definition freshening avoid xs :=
  rename_variables (fresh_id (avoid ++ xs)) (nodup variable_eq_dec xs).
Definition universalizing avoid xs :=
  let es := filter (fun x => negb (is_free x)) (nodup variable_eq_dec xs) in
  combine es (map (fun n => Var (Free n))
                  (seq (fresh_id (avoid ++ xs)) (List.length es))).

Lemma subst_atom_tag s a : atom_tag (subst_atom s a) = atom_tag a.
Proof. destruct a; reflexivity. Qed.
Lemma subst_product_length s p : List.length (subst_product s p) = List.length p.
Proof. apply map_length. Qed.
Lemma subst_product_app s p q :
  subst_product s (p ++ q) = subst_product s p ++ subst_product s q.
Proof. apply map_app. Qed.
Example substitution_is_simultaneous :
  subst_term [(Free 0, Var (Free 1)); (Free 1, zero)] (Var (Free 0))
  = Var (Free 1).
Proof. reflexivity. Qed.
