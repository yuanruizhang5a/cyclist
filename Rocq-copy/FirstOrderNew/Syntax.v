From Stdlib Require Import List Bool Arith ZArith String Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(** Terms and formulas use the same small first-order language as the source
    prover. [Free] variables are parameters; [Exist] variables are witnesses.
    A [product] is a conjunction of atoms, and a [formula] is a disjunction
    of products (disjunctive normal form). The empty product denotes truth;
    the empty formula denotes falsehood. *)
(** A predicate's [tag] reproduces its source-level logical annotation.
    Cyclic traces instead identify individual predicate occurrences, even when
    several occurrences share this tag. *)
Inductive variable := Free (id : nat) | Exist (id : nat).
Inductive term := Const (value : Z) | Var (name : variable)
  | Fun (symbol : string) (arguments : list term).
Inductive atom := Eq (left right : term) | Deq (left right : term)
  | Pred (tag : nat) (symbol : string) (arguments : list term).
Definition product := list atom.
Definition formula := list product.
Record sequent := { antecedent : formula; succedent : formula }.


(** Decidable *structural* equality, including predicate tags and list order.
    The boolean tests below are executable versions of these decisions. *)
Definition variable_eq_dec (x y : variable) : {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Fixpoint term_eq_dec (x y : term) : {x = y} + {x <> y}.
Proof.
  decide equality; try apply Z.eq_dec; try apply variable_eq_dec;
    try apply string_dec. apply list_eq_dec; apply term_eq_dec.
Defined.
Definition atom_eq_dec (x y : atom) : {x = y} + {x <> y}.
Proof.
  decide equality; try apply term_eq_dec; try apply Nat.eq_dec;
    try apply string_dec. apply list_eq_dec; apply term_eq_dec.
Defined.
Definition product_eq_dec := list_eq_dec atom_eq_dec.
Definition formula_eq_dec := list_eq_dec product_eq_dec.
Definition sequent_eq_dec (x y : sequent) : {x = y} + {x <> y}.
Proof. decide equality; apply formula_eq_dec. Defined.

Definition eqb_of_dec {A} (dec : forall x y : A, {x = y} + {x <> y}) x y :=
  if dec x y then true else false.

(** Connect the executable test to propositional equality once, so later
    proofs can reuse the same fact for every syntactic category. *)
Lemma eqb_of_dec_spec {A} dec (x y : A) :
  @eqb_of_dec A dec x y = true <-> x = y.
Proof. unfold eqb_of_dec; destruct (dec x y); intuition discriminate. Qed.
Definition variable_eqb := eqb_of_dec variable_eq_dec.
Definition term_eqb := eqb_of_dec term_eq_dec.
Definition atom_eqb := eqb_of_dec atom_eq_dec.
Definition product_eqb := eqb_of_dec product_eq_dec.
Definition sequent_eqb := eqb_of_dec sequent_eq_dec.
Lemma sequent_eqb_spec x y : sequent_eqb x y = true <-> x = y.
Proof. apply eqb_of_dec_spec. Qed.

(** Logical comparison ignores a predicate's annotation. Exact comparison
    above still distinguishes differently tagged atoms. *)
Definition erase_tag (a : atom) :=
  match a with Pred _ p ts => Pred 0 p ts | _ => a end.
Definition atom_logical_eqb a b := atom_eqb (erase_tag a) (erase_tag b).
Definition mem_atom a p := existsb (atom_eqb a) p.
Definition logical_mem a p := existsb (atom_logical_eqb a) p.
Definition product_subset p q := forallb (fun a => logical_mem a q) p.
(** [identityb] checks the sequent [antecedent |- succedent] by DNF inclusion.
    For each left product [p], some right product [q] must contain only atoms
    already present in [p]. Then [p] implies [q]. The original id test reversed
    these quantifiers. The empty cases follow the DNF meanings above. *)
Definition identityb j := forallb
  (fun p => existsb (fun q => product_subset q p) j.(succedent)) j.(antecedent).
(** Remove exact duplicates only: neither normalization changes logical tags
    or tries to prove two different products equivalent. *)
Definition normalize_product := nodup atom_eq_dec.
Definition normalize_formula f := nodup product_eq_dec (map normalize_product f).

(** Collect variables recursively, including those inside function arguments.
    Duplicates are retained; callers can remove them if they need a set. *)
Fixpoint term_vars t :=
  match t with
  | Const _ => [] | Var x => [x]
  | Fun _ ts => List.concat (map term_vars ts)
  end.
Definition atom_vars a :=
  match a with Eq t u | Deq t u => term_vars t ++ term_vars u
  | Pred _ _ ts => List.concat (map term_vars ts) end.
Definition product_vars p := List.concat (map atom_vars p).
Definition formula_vars f := List.concat (map product_vars f).
Definition sequent_vars j := formula_vars j.(antecedent) ++ formula_vars j.(succedent).
Definition is_free x := match x with Free _ => true | _ => false end.
Definition variable_id x := match x with Free n | Exist n => n end.
(** Choose an identifier above both free and existential identifiers in [xs].
    The next two lemmas justify using it as a fresh free variable. *)
Definition fresh_id xs := S (fold_right Nat.max 0 (map variable_id xs)).
Definition fresh_free xs := Free (fresh_id xs).
Lemma fresh_id_gt xs x : In x xs -> variable_id x < fresh_id xs.
Proof.
  unfold fresh_id. intro H. assert (variable_id x <= fold_right Nat.max 0
    (map variable_id xs)).
  { induction xs as [|a xs IH]; simpl in *; [contradiction|].
    destruct H as [<-|H]; [apply Nat.le_max_l|].
    eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r]. }
  lia.
Qed.
Lemma fresh_free_fresh xs : ~ In (fresh_free xs) xs.
Proof. intro H; pose proof (fresh_id_gt xs _ H); unfold fresh_free in *; cbn in *; lia. Qed.

(** Logical tags come from antecedent predicates; equal tags are collapsed.
    [retag] changes only a predicate annotation, never its symbol or arguments. *)
Definition atom_tag a := match a with Pred t _ _ => Some t | _ => None end.
Definition product_tags p := flat_map
  (fun a => match atom_tag a with Some t => [t] | None => [] end) p.
Definition logical_tags j := nodup Nat.eq_dec (flat_map product_tags j.(antecedent)).
Definition retag tag a := match a with Pred _ p ts => Pred tag p ts | _ => a end.
Definition zero := Const 0%Z.
Definition successor t := Fun "s" [t].
Definition cons t u := Fun "cons" [t; u].

(** Well-formed antecedents mention free variables only. The two update
    helpers remove every exact match; [replace_product] puts its replacement
    first, including when the old product was absent. *)
Definition antecedent_freeb j := forallb is_free (formula_vars j.(antecedent)).
Definition remove_atom a p := filter (fun b => negb (atom_eqb a b)) p.
Definition replace_product p q f := q :: filter (fun r => negb (product_eqb p r)) f.
(** Positions count *all* atoms in the flattened antecedent, starting at zero.
    [trace_tags] keeps only positions holding predicates, so its numbers can
    have gaps and differ from both logical tags and dense predicate ordinals. *)
Definition atom_positions (p : product) := combine (seq 0 (List.length p)) p.
Definition indexed_atoms j := combine
  (seq 0 (List.length (List.concat j.(antecedent)))) (List.concat j.(antecedent)).
Definition trace_tags j := flat_map
  (fun ia => match snd ia with Pred _ _ _ => [fst ia] | _ => [] end)
  (indexed_atoms j).

(** Small computations pin down three easy-to-miss conventions above. *)
Example nested_variables_are_collected :
  atom_vars (Pred 0 "LIST" [cons (Var (Free 2)) (Var (Free 3))])
  = [Free 2; Free 3].
Proof. reflexivity. Qed.
Example disjunctive_identity_bug_is_rejected :
  identityb {| antecedent := [[Eq (Var (Free 0)) zero]; [Eq (Var (Free 1)) zero]];
               succedent := [[Eq (Var (Free 0)) zero]] |} = false.
Proof. reflexivity. Qed.
Example shared_logical_tags_have_distinct_trace_ids :
  trace_tags {| antecedent := [[Pred 7 "P" [zero]; Pred 7 "Q" [zero]]];
                succedent := [] |} = [0; 1].
Proof. reflexivity. Qed.
