From Stdlib Require Import List Bool Arith String Lia.
From CyclistRocq.FirstOrderNew Require Export Rules.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

(** Executable proposals, not proofs. Every descriptor must be rechecked by a
    theorem-backed compiler. In particular, expected labels are never evidence.
    Indices refer to the supplied lists before rewriting or normalization. *)
Inductive rule_descriptor :=
| RDExFalso | RDIdentity
| RDTrivialEqualities
| RDLeftEquality (v : variable) (t : term)
| RDRightEquality (product_index : nat) (v : variable) (t : term)
| RDDischargeRight
| RDLeftInjective (product_index atom_index : nat)
| RDRightCongruence (product_index atom_index : nat)
| RDLeftDisjunction
| RDInstantiate (v : variable) (t : term)
| RDRightConjunction
| RDRightUnfold (product_index atom_index clause_index : nat)
| RDLeftUnfold (atom_index fresh_tag : nat)
| RDFold (clause_index : nat) (theta : substitution) (fresh_tag : nat)
| RDWeaken (target : sequent)
| RDSubstitute (theta : substitution) (target : sequent)
(** Native constructors have indexed, product-local instantiation, binary RHS
    splitting, and an occurrence-preserving unfolding layout. These explicit
    descriptors coexist with the older pure source proposal vocabulary. *)
| RDInstantiateAt (product_index : nat) (v : variable) (t : term)
| RDRightSplit (split_at : nat)
| RDLeftUnfoldAt (product_index atom_index fresh_tag : nat)
| RDRightUnfoldMatched (fuel product_index atom_index clause_index : nat)
| RDRightUnfoldInstance (product_index atom_index clause_index : nat)
    (theta : substitution).

Record rule_proposal := {
  proposal_descriptor : rule_descriptor;
  proposal_conclusion : sequent;
  proposal_premises : list sequent
}.
Definition propose rd j ks := {| proposal_descriptor := rd;
  proposal_conclusion := j; proposal_premises := ks |}.
Definition propose_unary rd j k := propose rd j [k].

Record generation_limits := {
  matching_fuel : nat;
  simplification_steps : nat;
  candidate_limit : nat;
  combination_limit : nat
}.
Definition default_generation_limits := {| matching_fuel := 32;
  simplification_steps := 32; candidate_limit := 256; combination_limit := 256 |}.
Fixpoint bounded_bind {A B} bound (f : A -> list B) xs := match xs with
  | [] => []
  | x::xs' => match bound with
    | 0 => []
    | S _ => let prefix := firstn bound (f x) in
      prefix ++ bounded_bind (bound - List.length prefix) f xs'
    end end.
Definition positions {A} (xs : list A) := combine (seq 0 (List.length xs)) xs.
Fixpoint replace_at {A} n (y : A) xs := match n,xs with
  | 0,_::xs' => y::xs'
  | S n',x::xs' => x::replace_at n' y xs'
  | _,[] => [] end.
Definition with_left j f := {| antecedent := f; succedent := j.(succedent) |}.
Definition with_right j f := {| antecedent := j.(antecedent); succedent := f |}.
Definition fresh_logical_tag j := S (fold_right Nat.max 0
  (logical_tags j)).
Definition existing_variables j := nodup variable_eq_dec (sequent_vars j).
Definition existential_variables xs := filter (fun v => negb (is_free v))
  (nodup variable_eq_dec xs).

(** Equalities/disequalities are unordered in the source sets. Preserve that
    convention without depending on the concrete order of reified lists. For
    tracked predicates neither side may discard a tracked logical tag. *)
Definition operation_atom_eqb tags a b := match a,b with
  | Eq t u,Eq v w | Deq t u,Deq v w =>
      (term_eqb t v && term_eqb u w) || (term_eqb t w && term_eqb u v)
  | Pred i p ts,Pred k q us => String.eqb p q &&
      eqb_of_dec (list_eq_dec term_eq_dec) ts us &&
      (if existsb (Nat.eqb i) tags || existsb (Nat.eqb k) tags
       then Nat.eqb i k else true)
  | _,_ => false end.
Definition operation_subset tags p q := forallb
  (fun a => existsb (operation_atom_eqb tags a) q) p.
Definition formula_entailsb tags stronger weaker := forallb
  (fun p => existsb (fun q => operation_subset tags q p) weaker) stronger.
(** [weakenableb tags j k]: the premise k is sufficient to conclude j. *)
Definition weakenableb tags j k :=
  formula_entailsb tags j.(antecedent) k.(antecedent) &&
  formula_entailsb [] k.(succedent) j.(succedent).

(** Free variables can only acquire free terms. Prime RHS variables can only
    undergo injective renaming, including those not explicitly bound by theta.
    This prevents capture of a still-unmapped prime variable. *)
Definition substitution_scopedb theta j :=
  forallb (fun xt => match fst xt with
    | Free _ => forallb is_free (term_vars (snd xt))
    | Exist _ => match snd xt with Var (Exist _) => true | _ => false end
    end) theta &&
  let es := existential_variables (sequent_vars j) in
  let images := map (fun v => subst_term theta (Var v)) es in
  Nat.eqb (List.length (nodup term_eq_dec images)) (List.length images).

Fixpoint first_available {A B} (f : A -> option B) xs := match xs with
  | [] => None
  | x::xs' => match f x with Some y => Some y | None => first_available f xs' end end.
Definition nonidentity_proposal rd j k :=
  if sequent_eqb j k then None else Some (propose_unary rd j k).
Definition safe_left_binding a :=
  let checked v t := if negb (term_eqb (Var v) t) &&
    is_free v && forallb is_free (term_vars t) then Some (v,t) else None in
  match a with
  | Eq t (Var v) => checked v t
  | Eq (Var v) t => checked v t
  | _ => None end.
Definition right_equality_binding a := match a with
  | Eq t (Var (Exist n)) => Some (Exist n,t)
  | Eq (Var (Exist n)) t => Some (Exist n,t)
  | _ => None end.
Definition trivial_proposal j :=
  let clean := filter (fun a => match a with
    | Eq t u => negb (term_eqb t u) | _ => true end) in
  nonidentity_proposal RDTrivialEqualities j
    {| antecedent := map clean j.(antecedent); succedent := map clean j.(succedent) |}.
Definition left_equality_proposal j := match j.(antecedent) with
  | [p] => match first_available safe_left_binding p with
    | Some (v,t) => nonidentity_proposal (RDLeftEquality v t) j
                    (subst_sequent [(v,t)] j)
    | None => None end
  | _ => None end.
Definition right_equality_proposal j := first_available (fun ip =>
  match first_available right_equality_binding (snd ip) with
  | Some (v,t) => nonidentity_proposal (RDRightEquality (fst ip) v t) j
      (with_right j (replace_at (fst ip) (subst_product [(v,t)] (snd ip))
                                 j.(succedent)))
  | None => None end) (positions j.(succedent)).
Definition discharge_right_proposal j := match j.(antecedent) with
  | [p] => nonidentity_proposal RDDischargeRight j (with_right j
      (map (fun q => filter (fun a =>
        negb (existsb (operation_atom_eqb [] a) p)) q) j.(succedent)))
  | _ => None end.
Definition safe_constructor_eqs injective a := match a with
  | Eq (Fun f ts) (Fun g us) =>
    if String.eqb f g && Nat.eqb (List.length ts) (List.length us) &&
       (negb injective || constructorb (Fun f ts))
    then Some (map (fun tu => Eq (fst tu) (snd tu)) (combine ts us))
    else None
  | _ => None end.
Definition expand_proposal (injective : bool) j :=
  let f := if injective then j.(antecedent) else j.(succedent) in
  first_available (fun ip => first_available (fun ia =>
    match safe_constructor_eqs injective (snd ia) with
    | Some eqs =>
      let p := normalize_product (eqs ++ remove_atom (snd ia) (snd ip)) in
      let f' := replace_at (fst ip) p f in
      nonidentity_proposal
        (if injective then RDLeftInjective (fst ip) (fst ia)
         else RDRightCongruence (fst ip) (fst ia)) j
        (if injective then with_left j f' else with_right j f')
    | None => None end) (positions (snd ip))) (positions f).
(** Source greedy simplifier order, with safe free/prime scopes. *)
Definition simplification_proposal j := first_available (fun f => f j)
  [trivial_proposal; left_equality_proposal; right_equality_proposal;
   discharge_right_proposal; expand_proposal true; expand_proposal false].
Definition axiom_proposals j :=
  if contradictionb j then [propose RDExFalso j []]
  else if identityb j then [propose RDIdentity j []] else [].
Definition left_split_proposals j :=
  if 2 <=? List.length j.(antecedent)
  then [propose RDLeftDisjunction j (lhs_split j)] else [].
Definition instantiate_proposals limits j :=
  let vs := existing_variables j in
  bounded_bind limits.(candidate_limit) (fun v =>
    map (fun u => propose_unary (RDInstantiate v (Var u)) j
      (subst_sequent [(v,Var u)] j)) (filter is_free vs))
    (filter (fun v => negb (is_free v)) vs).
Fixpoint prime_disjointb (p : product) := match p with
  | [] => true
  | a::p' =>
    forallb (fun v => negb (existsb (variable_eqb v) (product_vars p')))
      (existential_variables (atom_vars a)) && prime_disjointb p' end.
Definition right_split_proposals j := match j.(succedent) with
  | [p] => if (2 <=? List.length p) && prime_disjointb p then
      [propose RDRightConjunction j (map (fun a => with_right j [[a]]) p)]
      else []
  | _ => [] end.

(** Fresh right clause variables are ALL existential, including source free
    clause locals. Left clauses are ALL fresh free eigenvariables. The naming
    convention of the source clause never leaks into the RHS quantifier scope. *)
Definition fresh_clause_as (existential : bool) avoid c :=
  let vs := nodup variable_eq_dec (clause_vars c) in
  let start := fresh_id (avoid ++ vs) in
  let theta := combine vs (map (fun n => Var
    (if existential then Exist n else Free n)) (seq start (List.length vs))) in
  subst_clause theta c.
Definition right_unfold_at limits d j pi ai ci : option rule_proposal :=
  match nth_error j.(succedent) pi,nth_error d ci with
  | Some p,Some c => match nth_error p ai with
    | Some (Pred tag name args) =>
      if String.eqb name c.(clause_name) then
        let c' := fresh_clause_as true (sequent_vars j) c in
        match head_match_terms limits.(matching_fuel) [] c'.(head) args with
        | Some (theta,eqs) =>
          let q := normalize_product
            (remove_atom (Pred tag name args) p ++
             subst_product theta c'.(body) ++ eqs) in
          Some (propose_unary (RDRightUnfold pi ai ci) j
            (with_right j (replace_at pi q j.(succedent))))
        | None => None end
      else None
    | _ => None end
  | _,_ => None end.
Definition option_list {A} (x : option A) := match x with
  | Some y => [y] | None => [] end.
Definition right_unfold_proposals limits d j :=
  bounded_bind limits.(candidate_limit) (fun ic =>
    bounded_bind limits.(candidate_limit) (fun ip =>
      bounded_bind limits.(candidate_limit) (fun ia =>
        option_list (right_unfold_at limits d j (fst ip) (fst ia) (fst ic)))
        (positions (snd ip))) (positions j.(succedent))) (positions d).
Definition left_unfold_at d j ai : option rule_proposal := match j.(antecedent) with
  | [p] => match nth_error p ai with
    | Some (Pred tag name args) =>
      let cs := clauses_for d name in
      if negb (Nat.eqb (List.length cs) 0) &&
        forallb (fun c => Nat.eqb (List.length c.(head)) (List.length args)) cs then
        let fresh := fresh_logical_tag j in
        let context := retag fresh (Pred tag name args) ::
                       remove_atom (Pred tag name args) p in
        let ks := map (fun c =>
          let c' := fresh_clause_as false (sequent_vars j) c in
          with_left j [normalize_product (context ++
            map (fun tu => Eq (fst tu) (snd tu)) (combine args c'.(head)) ++
            map (retag tag) c'.(body))]) cs in
        Some (propose (RDLeftUnfold ai fresh) j ks)
      else None
    | _ => None end
  | _ => None end.
Definition left_unfold_proposals limits d j := match j.(antecedent) with
  | [p] => bounded_bind limits.(candidate_limit)
      (fun ia => option_list (left_unfold_at d j (fst ia))) (positions p)
  | _ => [] end.

(** Bounded directional matching. A final simultaneous-substitution check below
    is essential: partial matches alone are not certificates. *)
Definition match_atom_candidates fuel theta a b := match a,b with
  | Pred _ p ts,Pred _ q us => if String.eqb p q then
      match match_terms fuel theta ts us with Some s => [s] | None => [] end
      else []
  | Eq t u,Eq v w | Deq t u,Deq v w =>
      (match match_terms fuel theta [t;u] [v;w] with
       | Some s => [s] | None => [] end) ++
      (match match_terms fuel theta [t;u] [w;v] with
       | Some s => [s] | None => [] end)
  | _,_ => [] end.
Fixpoint bounded_match_product bound fuel theta p q := match p with
  | [] => firstn bound [theta]
  | a::p' => bounded_bind bound (fun b => bounded_bind bound
      (fun theta' => bounded_match_product bound fuel theta' p' q)
      (match_atom_candidates fuel theta a b)) q end.
Fixpoint bounded_match_right_product bound fuel theta p q := match p with
  | [] => firstn bound [theta]
  | a::p' => bounded_bind bound (fun b => bounded_bind bound
      (fun theta' => bounded_match_right_product bound fuel theta' p' q)
      (match_atom_candidates fuel theta b a)) q end.
Fixpoint match_left_formulas bound fuel theta targets sources := match sources with
  | [] => firstn bound [theta]
  | p::ps => bounded_bind bound (fun q => bounded_bind bound
      (fun theta' => match_left_formulas bound fuel theta' targets ps)
      (bounded_match_product bound fuel theta q p)) targets end.
Fixpoint match_right_formulas bound fuel theta sources targets := match targets with
  | [] => firstn bound [theta]
  | q::qs => bounded_bind bound (fun p => bounded_bind bound
      (fun theta' => match_right_formulas bound fuel theta' sources qs)
      (bounded_match_right_product bound fuel theta p q)) sources end.
Definition fold_proposals limits d j := match j.(antecedent) with
  | [p] => bounded_bind limits.(candidate_limit) (fun ic =>
    let c := fresh_clause_as false (sequent_vars j) (snd ic) in
    if Nat.eqb (List.length c.(body)) 0 then [] else
    bounded_bind limits.(candidate_limit) (fun theta =>
      let instance := subst_product theta c.(body) in
      if substitution_freeb theta && operation_subset [] instance p then
        let remainder := filter (fun a =>
          negb (existsb (operation_atom_eqb [] a) instance)) p in
        let tag := fresh_logical_tag j in
        let k := with_left j [normalize_product
          (Pred tag c.(clause_name) (map (subst_term theta) c.(head)) :: remainder)] in
        [propose_unary (RDFold (fst ic) theta tag) j k]
      else [])
      (bounded_match_product limits.(candidate_limit) limits.(matching_fuel)
        [] c.(body) p)) (positions d)
  | _ => [] end.

Record backlink_plan := {
  backlink_source : sequent;
  backlink_target_index : nat;
  backlink_target : sequent;
  backlink_substitution : substitution;
  backlink_instance : sequent;
  backlink_preserved_tags : list nat;
  backlink_preparation : list rule_proposal;
  backlink_exact_edge : trace_edge
}.
Fixpoint insert_tag t tags := match tags with
  | [] => [t] | u::tags' => if t <=? u then t::tags else u::insert_tag t tags' end.
Fixpoint ordered_tags tags := match tags with
  | [] => [] | t::tags' => insert_tag t (ordered_tags tags') end.
Definition shared_tags j k := ordered_tags (filter
  (fun t => existsb (Nat.eqb t) (logical_tags k)) (logical_tags j)).
Definition same_formula_shapesb j k :=
  Bool.eqb (Nat.eqb (List.length j.(antecedent)) 1)
           (Nat.eqb (List.length k.(antecedent)) 1) &&
  Bool.eqb (Nat.eqb (List.length j.(succedent)) 1)
           (Nat.eqb (List.length k.(succedent)) 1).
Definition retain_backlink_tags j k tags := fold_left (fun kept tag =>
  if weakenableb (kept ++ [tag]) j k then kept ++ [tag] else kept) tags [].
Definition exact_backlink_edge j tags := {| continuations := flat_map
  (fun ia => match snd ia with
    | Pred tag _ _ => if existsb (Nat.eqb tag) tags then [(fst ia,fst ia)] else []
    | _ => [] end) (indexed_atoms j); progressing := [] |}.
Definition make_backlink_plan j target_index k theta : option backlink_plan :=
  let instance := subst_sequent theta k in
  let kept := retain_backlink_tags j instance (shared_tags j k) in
  if substitution_scopedb theta k && weakenableb [] j instance &&
     negb (Nat.eqb (List.length kept) 0) && weakenableb kept j instance then
    let weaken_steps := if sequent_eqb j instance then []
      else [propose_unary (RDWeaken instance) j instance] in
    let subst_steps := if substitution_identityb theta then []
      else [propose_unary (RDSubstitute theta k) instance k] in
    Some {| backlink_source := j; backlink_target_index := target_index;
      backlink_target := k; backlink_substitution := theta;
      backlink_instance := instance; backlink_preserved_tags := kept;
      backlink_preparation := weaken_steps ++ subst_steps;
      backlink_exact_edge := exact_backlink_edge k kept |}
  else None.
Definition backlink_plans_for limits j target_index k :=
  if same_formula_shapesb j k &&
     negb (Nat.eqb (List.length (shared_tags j k)) 0) then
    let left_matches := match_left_formulas limits.(candidate_limit)
      limits.(matching_fuel) [] k.(antecedent) j.(antecedent) in
    bounded_bind limits.(candidate_limit) (fun theta =>
      bounded_bind limits.(candidate_limit) (fun theta' =>
        option_list (make_backlink_plan j target_index k theta'))
        (match_right_formulas limits.(candidate_limit) limits.(matching_fuel)
          theta j.(succedent) k.(succedent))) left_matches
  else [].
(** The caller supplies ALL graph nodes; only the source index is removed.
    Closed nodes and siblings remain eligible, as in source all_nodes. *)
Definition backlink_plans limits source_index j nodes :=
  bounded_bind limits.(candidate_limit) (fun ik =>
    if Nat.eqb source_index (fst ik) then []
    else backlink_plans_for limits j (fst ik) (snd ik)) nodes.
Definition backlink_plans_all limits j nodes :=
  bounded_bind limits.(candidate_limit) (fun ik =>
    backlink_plans_for limits j (fst ik) (snd ik)) nodes.

(** Programs express source composition without flattening intermediate proof
    nodes. A compiler checks each application, then inserts its actual premises.
    Open frontiers are returned to DFS; backlinks have no open frontier. *)
Inductive rule_program :=
| ProgramOpen (label : sequent)
| ProgramApply (proposal : rule_proposal) (children : list rule_program)
| ProgramBacklink (plan : backlink_plan).
Definition program_input p := match p with
  | ProgramOpen j => j | ProgramApply r _ => r.(proposal_conclusion)
  | ProgramBacklink b => b.(backlink_source) end.
Definition primitive_program p := ProgramApply p (map ProgramOpen p.(proposal_premises)).
Fixpoint program_frontier p := match p with
  | ProgramOpen j => [j]
  | ProgramApply _ ps => List.concat (map program_frontier ps)
  | ProgramBacklink _ => [] end.
Definition terminal_program j := match axiom_proposals j with
  | p::_ => primitive_program p | [] => ProgramOpen j end.
Fixpoint normalize_program fuel j :=
  match simplification_proposal j with
  | None => terminal_program j
  | Some p => match fuel with
    | 0 => ProgramOpen j
    | S fuel' => match p.(proposal_premises) with
      | [k] => ProgramApply p [normalize_program fuel' k]
      | _ => primitive_program p end end end.
Definition wrapped_program limits p := ProgramApply p
  (map (normalize_program limits.(simplification_steps)) p.(proposal_premises)).
Fixpoint bounded_combinations {A} bound (choices : list (list A)) : list (list A) :=
  match choices with
  | [] => firstn bound [[]]
  | xs::rest => bounded_bind bound (fun x =>
      map (List.cons x) (bounded_combinations bound rest)) xs end.
(** Bind all open frontiers, preserving closed branches and intermediate nodes.
    This is the source [compose], including all combinations across L.Unf cases. *)
Fixpoint bind_program bound (next : sequent -> list rule_program) p := match p with
  | ProgramOpen j => firstn bound (next j)
  | ProgramBacklink _ => firstn bound [p]
  | ProgramApply r ps => map (ProgramApply r)
      (bounded_combinations bound (map (bind_program bound next) ps)) end.
Definition combined_unfold_programs limits d j :=
  bounded_bind limits.(combination_limit) (fun p =>
    bind_program limits.(combination_limit)
      (fun k => match simplification_proposal k with
        | Some _ => []
        | None => map (wrapped_program limits) (right_unfold_proposals limits d k)
        end)
      (wrapped_program limits p)) (left_unfold_proposals limits d j).
(** After folding, the source is a NEW premise node. Every supplied old node,
    including the pre-fold conclusion, is an eligible other-node target. *)
Definition fold_backlink_programs limits d j nodes :=
  bounded_bind limits.(combination_limit) (fun p =>
    bind_program limits.(combination_limit)
      (fun k => map ProgramBacklink (backlink_plans_all limits k nodes))
      (primitive_program p)) (fold_proposals limits d j).

Record rule_menu := {
  menu_axioms : list rule_program;
  menu_simplifications : list rule_program;
  menu_choices : list rule_program
}.
(** Greedy families are separate so the searcher cannot fall through to choices
    after choosing simplification. Choice order is source order; fold programs
    exist only when their immediate backlink can be planned. *)
Definition source_choice_programs limits d source_index j nodes :=
  map ProgramBacklink (backlink_plans limits source_index j nodes) ++
  map (wrapped_program limits) (left_split_proposals j) ++
  map (wrapped_program limits) (instantiate_proposals limits j) ++
  map (wrapped_program limits) (right_split_proposals j) ++
  map (wrapped_program limits) (right_unfold_proposals limits d j) ++
  combined_unfold_programs limits d j ++
  map (wrapped_program limits) (left_unfold_proposals limits d j) ++
  fold_backlink_programs limits d j nodes.
Definition source_rule_menu limits d source_index j nodes :=
  match axiom_proposals j with
  | p::ps => {| menu_axioms := map primitive_program (p::ps);
               menu_simplifications := []; menu_choices := [] |}
  | [] => match simplification_proposal j with
    | Some p => {| menu_axioms := []; menu_simplifications := [wrapped_program limits p];
                  menu_choices := [] |}
    | None => {| menu_axioms := []; menu_simplifications := [];
                 menu_choices := source_choice_programs limits d source_index j nodes |}
    end end.

(** The public primitive stream is useful for compilers and independent local
    testing. RDFold here is a primitive, whereas source_rule_menu enforces its
    immediate-backlink restriction. *)
Definition primitive_rule_proposals limits d j :=
  axiom_proposals j ++ option_list (simplification_proposal j) ++
  left_split_proposals j ++ instantiate_proposals limits j ++
  right_split_proposals j ++ right_unfold_proposals limits d j ++
  left_unfold_proposals limits d j ++ fold_proposals limits d j.

Lemma bounded_bind_length {A B} bound (f : A -> list B) xs :
  List.length (bounded_bind bound f xs) <= bound.
Proof.
  revert bound; induction xs as [|x xs IH]; intro bound; [cbn; lia|].
  destruct bound as [|bound]; [cbn; lia|].
  cbn [bounded_bind]. rewrite length_app.
  pose proof (IH (S bound - List.length (firstn (S bound) (f x)))).
  assert (List.length (firstn (S bound) (f x)) <= S bound).
  { rewrite length_firstn; apply Nat.le_min_l. }
  lia.
Qed.
Lemma backlink_plans_length limits i j nodes :
  List.length (backlink_plans limits i j nodes) <= limits.(candidate_limit).
Proof. apply bounded_bind_length. Qed.
Lemma right_unfold_proposals_length limits d j :
  List.length (right_unfold_proposals limits d j) <= limits.(candidate_limit).
Proof. apply bounded_bind_length. Qed.
Lemma planned_backlink_instance j i k theta b :
  make_backlink_plan j i k theta = Some b ->
  b.(backlink_instance) = subst_sequent b.(backlink_substitution) b.(backlink_target).
Proof.
  unfold make_backlink_plan. destruct (_ && _ && _ && _)%bool;
    intro H; try discriminate; inversion H; reflexivity.
Qed.
