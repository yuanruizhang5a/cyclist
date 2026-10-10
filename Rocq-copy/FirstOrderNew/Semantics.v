From Stdlib Require Import List Bool Arith ZArith String Lia Classical_Prop.
From CyclistRocq.FirstOrderNew Require Export Definitions.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(** Semantic interpretation of the syntax exported by [Definitions].
    Here [d] is a list of defining clauses, [m] is a model, [rho] is a
    variable assignment, and [j] is a sequent. Truth is expressed in Rocq's
    [Prop], rather than computed by a Boolean test.

    The file builds predicate truth from finite clause derivations, defines
    sequent validity, then equips antecedent occurrences with finite bounds
    for cyclic traces. The final lemmas justify identity and substitution. *)

(** A model interprets terms in an arbitrary domain [carrier]. Integer
    literals are interpreted by [constant_value]; function symbols and their
    evaluated argument lists are interpreted by [function_value].

    The remaining fields are proofs of the constructor properties used by
    first-order rules: unary "s" and binary "cons" are injective, and neither
    can produce the value of zero. No freeness of other function symbols,
    distinctness of different integer literals, or disjointness between "s"
    and "cons" is assumed. Inductive predicates are defined separately below. *)
Record model := {
  carrier : Type;
  constant_value : Z -> carrier;
  function_value : string -> list carrier -> carrier;
  successor_injective : forall x y,
    function_value "s" [x] = function_value "s" [y] -> x = y;
  cons_injective : forall x y u v,
    function_value "cons" [x;y] = function_value "cons" [u;v] -> x = u /\ y = v;
  zero_not_successor : forall x, constant_value 0%Z <> function_value "s" [x];
  zero_not_cons : forall x y, constant_value 0%Z <> function_value "cons" [x;y]
}.
(** A valuation assigns a domain element to every variable, including both
    [Free n] parameters and [Exist n] witness variables. At this level neither
    kind is quantified; quantification is introduced by [valid]/[eval_right]. *)
Definition valuation (m : model) := variable -> carrier m.
(** Evaluate a term recursively: interpret a literal, look up a variable,
    or evaluate every function argument before applying [function_value].
    For example, [Fun "s" [Var x]] denotes [function_value m "s" [rho x]]. *)
Fixpoint eval_term m (rho : valuation m) t : carrier m := match t with
  | Const z => constant_value m z | Var x => rho x
  | Fun f ts => function_value m f (map (eval_term m rho) ts) end.
(** A predicate interpretation maps a symbol and a list of domain elements
    to a proposition. This lets the same evaluator use either a finite stage
    or the full inductive interpretation of predicates. *)
Definition relation m := string -> list (carrier m) -> Prop. (* It is an interpretation of predicates *)
(** Interpret an atom using the supplied predicate relation [r]. [Eq] and
    [Deq] mean equality and inequality of evaluated terms. [Pred] applies [r]
    to evaluated arguments; its logical tag is ignored for truth. *)
Definition eval_atom_with m (r : relation m) rho a := match a with
  | Eq t u => eval_term m rho t = eval_term m rho u
  | Deq t u => eval_term m rho t <> eval_term m rho u
  | Pred _ p ts => r p (map (eval_term m rho) ts) end.
(** A product is a conjunction: [Forall] requires every atom in its list
    to hold under the same valuation and relation. The empty product is true. *)
Definition eval_product_with m r rho p := Forall (eval_atom_with m r rho) p.

(** Finite approximations to inductive predicate truth. Stage zero contains
    no predicate instances. At stage [S k], an instance holds when some clause
    in [d] has its symbol and some valuation makes the head equal its arguments
    and the body true, interpreting body predicates at stage [k].

    The clause valuation supplies values for all clause variables, independently
    of any valuation at the call site. Equalities/inequalities do not consume
    predicate stages. A clause with an empty body can yield facts at stage one;
    recursive calls require earlier stages, so circular support alone cannot
    establish truth. *)
Fixpoint stage d m (n : nat) : relation m := match n with
  | 0 => fun _ _ => False
  | S k => fun p args => exists c, In c d /\ clause_name c = p /\
      exists rho : valuation m,
        map (eval_term m rho) (head c) = args /\
        eval_product_with m (stage d m k) rho (body c)
  end. 
(** An inductive instance is true if it appears at some finite stage.
    This union of stages gives finite derivations only. [inductive_unfold]
    and [inductive_least] below establish its least-fixed-point meaning. *)
Definition inductive_relation d m : relation m :=
  fun p args => exists n, stage d m n p args.
(** Atom truth with predicates interpreted by the clauses in [d], using
    their full inductive relation rather than a chosen finite stage. *)
Definition eval_atom d m := eval_atom_with m (inductive_relation d m).
(** Conjunction truth under the full inductive predicate interpretation.
    All atoms share the valuation [rho] supplied when this function is used. *)
Definition eval_product d m := eval_product_with m (inductive_relation d m).
(** A formula is a disjunction of products: at least one listed product
    must hold under [rho]. The empty formula is false. This evaluator keeps
    the values of both free and existential variables fixed by [rho]. *)
Definition eval_formula d m rho f := exists p, In p f /\ eval_product d m rho p.
(** [sigma] agrees with [rho] on every free parameter. It may assign
    different values to existential variables; the order of the arguments
    matches the base valuation [rho] and the chosen witness valuation [sigma]. *)
Definition agrees_free m (rho sigma : valuation m) := forall n, sigma (Free n) = rho (Free n).
(** Truth on the right of a sequent allows witnesses: choose a product and
    one valuation [sigma] that satisfies all its atoms while preserving [rho]'s
    free parameters. Existential variables may be reassigned together, so
    repeated occurrences of a witness variable still denote the same value. *)
Definition eval_right d m rho f := exists p, In p f /\
  exists sigma : valuation m, agrees_free m rho sigma /\ eval_product d m sigma p.
(** A sequent is valid when, in every model and for every valuation [rho],
    truth of its antecedent implies right-side truth with suitable witnesses.
    Well-formed antecedents contain only free variables (checked elsewhere
    by [antecedent_freeb]); [valid] itself imposes no well-formedness check. *)
Definition valid d j := forall m (rho : valuation m),
  eval_formula d m rho j.(antecedent) -> eval_right d m rho j.(succedent).

(** Enlarging the predicate relation preserves conjunction truth. Only
    predicate atoms depend on the relation; equality and inequality do not. *)
Lemma product_monotone m r s rho p :
  (forall name args, r name args -> s name args) ->
  eval_product_with m r rho p -> eval_product_with m s rho p.
Proof.
  intros Hrs Hp. eapply Forall_impl; [|exact Hp]. intros a Ha.
  destruct a; cbn in *; auto.
Qed.
(** Every stage is included in the next: a derivation remains available
    when its body predicates are allowed one more stage. *)
Lemma stage_step d m n : forall p args,
  stage d m n p args -> stage d m (S n) p args.
Proof.
  induction n as [|n IH]; cbn; [contradiction|].
  intros p args [c [Hc [Hname [rho [Hhead Hbody]]]]].
  exists c; repeat split; try assumption. exists rho; split; [exact Hhead|].
  eapply product_monotone; [exact IH|exact Hbody].
Qed.
(** Generalize [stage_step] to any larger bound [k]. Later proofs use this
    to put several derivations under one common stage bound. *)
Lemma stage_le d m n k : n <= k -> forall p args,
  stage d m n p args -> stage d m k p args.
Proof.
  intro H; induction H; intros p args Hp; [exact Hp|].
  apply stage_step; auto.
Qed.
(** Every true atom has a finite stage bound. Predicate truth supplies
    that bound; equality and inequality can use zero since they ignore stages. *)
Lemma atom_stage_bound d m rho a : eval_atom d m rho a ->
  exists n, eval_atom_with m (stage d m n) rho a.
Proof. destruct a; cbn; intro H; try (exists 0; exact H); exact H. Qed.
(** A true finite conjunction has a single stage bound for all its atoms.
    The proof takes maxima of the individual bounds and uses stage monotonicity.
    This finite-list fact is what lets the union of stages satisfy clauses. *)
Lemma product_stage_bound d m rho p : eval_product d m rho p ->
  exists n, eval_product_with m (stage d m n) rho p.
Proof.
  intro H; induction H as [|a p Ha Hp [k Hk]].
  - exists 0; constructor.
  - destruct (atom_stage_bound d m rho a Ha) as [n Hn].
    exists (Nat.max n k); constructor.
    + destruct a; cbn in *; try exact Hn.
      eapply stage_le; [apply Nat.le_max_l|exact Hn].
    + eapply product_monotone; [|exact Hk].
      intros name args Hargs; eapply stage_le; [apply Nat.le_max_r|exact Hargs].
Qed.

(** Worlds record finite derivation bounds for individual antecedent
    occurrences. Quantifying over these bounds is equivalent to ordinary
    least-fixed-point validity, as proved below. Logical tags may be shared. *)
(** Conjunction truth with a separate bound for each atom occurrence.
    The first atom uses [bounds start], the next [bounds (S start)], and so on.
    Positions count equality and inequality atoms too, although their truth
    does not depend on the bound. The empty product is true at any offset. *)
Fixpoint bounded_product d m rho (bounds : nat -> nat) start p : Prop :=
  match p with [] => True | a::p' =>
    eval_atom_with m (stage d m (bounds start)) rho a /\
    bounded_product d m rho bounds (S start) p' end.
(** Discard occurrence bounds: each bounded predicate instance belongs
    to [inductive_relation], so the product is true in the ordinary semantics. *)
Lemma bounded_product_forget d m rho bounds start p :
  bounded_product d m rho bounds start p -> eval_product d m rho p.
Proof.
  revert start; induction p as [|a p IH]; intros start H; constructor.
  - destruct H as [Ha Hp]; destruct a; cbn in *; try exact Ha.
    exists (bounds start); exact Ha.
  - apply (IH (S start)); exact (proj2 H).
Qed.
(** A product true at stage [n] can use the constant bound function
    [fun _ => n], regardless of its starting occurrence position. *)
Lemma bounded_product_uniform d m rho n start p :
  eval_product_with m (stage d m n) rho p ->
  bounded_product d m rho (fun _ => n) start p.
Proof. intro H; revert start; induction H; cbn; auto. Qed.
(** A world packages a model and its valuation with a selected antecedent
    disjunct [active_product] (a zero-based product index) and a bound function.
    [world_bounds] is indexed by absolute atom positions in the flattened
    antecedent, not by predicate annotations. Bounds need not be minimal, and
    arbitrary records need not make the selected product hold; [active_holds]
    states that additional condition. *)
Record world := { world_model : model;
  world_valuation : valuation world_model; active_product : nat;
  world_bounds : nat -> nat }.
(** Count all atoms in products before the selected product. This converts
    its local atom indices into positions in the flattened antecedent.
    For product lengths [2; 3], selecting product one gives offset two. *)
Definition active_offset j w := List.length
  (List.concat (firstn w.(active_product) j.(antecedent))).
(** Require that the selected antecedent product exists and holds with
    the world's occurrence bounds, starting at its absolute offset.
    An out-of-range product index makes this proposition false. *)
Definition active_holds d j w := exists p,
  nth_error j.(antecedent) w.(active_product) = Some p /\
  bounded_product d w.(world_model) w.(world_valuation) w.(world_bounds)
    (active_offset j w) p.
(** The sequent proposition at one world: if its selected, bounded
    antecedent product holds, the succedent has witnesses. This is the form
    used by the cyclic framework; when [active_holds] is false it holds vacuously. *)
Definition denote d j w := active_holds d j w ->
  eval_right d w.(world_model) w.(world_valuation) j.(succedent).
(** Ordinary validity is equivalent to [denote] holding in every world.
    One direction forgets bounds; the other selects a true antecedent product
    and gives all its occurrences a uniform finite bound. Thus the extra world
    data needed for traces does not change which sequents are valid. *)
Lemma valid_iff_worlds d j : valid d j <-> forall w, denote d j w.
Proof.
  split.
  - intros H [m rho i bounds] [p [Hi Hp]]. apply H. exists p; split.
    + eapply nth_error_In; exact Hi.
    + eapply bounded_product_forget; exact Hp.
  - intros H m rho [p [Hp Htruth]]. apply In_nth_error in Hp.
    destruct Hp as [i Hi]. destruct (product_stage_bound d m rho p Htruth) as [n Hn].
    apply (H {| world_model := m; world_valuation := rho; active_product := i;
      world_bounds := fun _ => n |}). exists p; split; [exact Hi|].
    cbn [world_model world_valuation world_bounds].
    apply bounded_product_uniform; exact Hn.
Qed.
(** The full inductive relation satisfies exactly one clause-unfolding
    step: a predicate instance holds iff a matching clause has a valuation
    with the required head values and a true body. For the reverse direction,
    [product_stage_bound] places the whole body at one finite stage. *)
Theorem inductive_unfold d m p args : inductive_relation d m p args <->
  exists c, In c d /\ clause_name c = p /\ exists rho : valuation m,
    map (eval_term m rho) (head c) = args /\ eval_product d m rho (body c).
Proof.
  split.
  - intros [[|n] H]; [contradiction|].
    destruct H as [c [Hc [Hname [rho [Hhead Hbody]]]]].
    exists c; repeat split; try assumption. exists rho; split; [exact Hhead|].
    eapply product_monotone; [|exact Hbody]. intros name xs Hx; exists n; exact Hx.
  - intros [c [Hc [Hname [rho [Hhead Hbody]]]]].
    destruct (product_stage_bound d m rho (body c) Hbody) as [n Hn].
    exists (S n), c; repeat split; try assumption. exists rho; auto.
Qed.
(** The inductive relation is contained in every relation [r] closed under
    the clauses of [d]. [Hclosed] says that a true clause body yields its head
    in [r]. Together with [inductive_unfold], this proves that our interpretation
    is the least fixed point, rather than one admitting unsupported cycles. *)
Theorem inductive_least d m (r : relation m)
  (Hclosed : forall c rho, In c d -> eval_product_with m r rho (body c) ->
    r (clause_name c) (map (eval_term m rho) (head c))) :
  forall p args, inductive_relation d m p args -> r p args.
Proof.
  intros p args [n Hn]; revert p args Hn.
  induction n as [|n IH]; [cbn; contradiction|].
  intros p args [c [Hc [<- [rho [<- Hbody]]]]]. apply Hclosed; [exact Hc|].
  eapply product_monotone; [exact IH|exact Hbody].
Qed.

(** Replacing a predicate's tag by zero preserves truth: annotations are
    syntactic metadata and are ignored by the atom evaluator. *)
Lemma eval_atom_erase d m rho a : eval_atom d m rho (erase_tag a) <-> eval_atom d m rho a.
Proof. destruct a; reflexivity. Qed.
(** The Boolean comparison that ignores tags implies semantic equivalence
    of the compared atoms. This bridges executable syntax tests and truth. *)
Lemma eval_atom_logical_eq d m rho a b : atom_logical_eqb a b = true ->
  (eval_atom d m rho a <-> eval_atom d m rho b).
Proof.
  unfold atom_logical_eqb; intro H; apply eqb_of_dec_spec in H.
  rewrite <- eval_atom_erase, <- (eval_atom_erase d m rho b), H; reflexivity.
Qed.
(** If every atom of [p] occurs in [q] up to logical equality, truth of
    [q] implies truth of [p]. The implication runs from the larger conjunction
    to the smaller one; duplicate atoms and differing tags cause no problem. *)
Lemma product_subset_sound d m rho p q : product_subset p q = true ->
  eval_product d m rho q -> eval_product d m rho p.
Proof.
  intros Hsub Hq. apply Forall_forall; intros a Ha.
  apply forallb_forall with (x:=a) in Hsub; [|exact Ha].
  apply existsb_exists in Hsub; destruct Hsub as [b [Hb Heq]].
  apply (proj2 (eval_atom_logical_eq d m rho a b Heq)).
  apply Forall_forall with (x:=b) in Hq; auto.
Qed.
(** The executable identity check proves validity: every antecedent
    product has a succedent product whose atoms it already implies. The proof
    chooses that product and reuses [rho] as the right-side witness valuation. *)
Theorem identity_sound d j : identityb j = true -> valid d j.
Proof.
  intros H m rho [p [Hp Htruth]].
  apply forallb_forall with (x:=p) in H; [|exact Hp].
  apply existsb_exists in H; destruct H as [q [Hq Hsub]].
  exists q; split; [exact Hq|]. exists rho; split; [intro n; reflexivity|].
  eapply product_subset_sound; eauto.
Qed.

(** Induction for terms with an induction hypothesis for every argument of
    [Fun f ts], expressed by [Forall P ts]. This handles the nested [list term]
    structure explicitly, so evaluation/substitution proofs can recurse into
    every function argument. *)
Lemma term_induction (P : term -> Prop)
  (HC : forall z, P (Const z)) (HV : forall x, P (Var x))
  (HF : forall f ts, Forall P ts -> P (Fun f ts)) : forall t, P t.
Proof.
  fix IH 1; intro t; destruct t.
  - apply HC.
  - apply HV.
  - apply HF. induction arguments; constructor; auto.
Qed.
(** Turn a syntactic substitution [s] into a valuation: the value of [x]
    is obtained by evaluating its replacement [lookup s x] under [rho]. An
    unmapped variable keeps its old value. Replacements are evaluated directly
    under [rho], matching simultaneous (not repeated) substitution. *)
Definition subst_valuation m s (rho : valuation m) : valuation m :=
  fun x => eval_term m rho (lookup s x).
(** Substitution commutes with term evaluation: substituting syntax then
    evaluating under [rho] equals evaluating the original term under the
    valuation induced by that substitution. *)
Lemma eval_subst_term m s rho t : eval_term m rho (subst_term s t) =
  eval_term m (subst_valuation m s rho) t.
Proof.
  induction t using term_induction; cbn; try reflexivity.
  f_equal. rewrite map_map. apply map_ext_in; intros t Ht.
  apply Forall_forall with (x:=t) in H; auto.
Qed.
(** Lift the substitution/evaluation correspondence to atom truth.
    The same inductive predicate interpretation is used on both sides. *)
Lemma eval_subst_atom d m s rho a :
  eval_atom d m rho (subst_atom s a) <-> eval_atom d m (subst_valuation m s rho) a.
Proof.
  destruct a; cbn; try (rewrite !eval_subst_term; reflexivity).
  rewrite map_map. assert (map (fun t => eval_term m rho (subst_term s t)) arguments =
    map (eval_term m (subst_valuation m s rho)) arguments).
  { apply map_ext; apply eval_subst_term. } rewrite H; reflexivity.
Qed.
(** Lift the atom correspondence to a whole conjunction, preserving the
    shared valuation of every variable. Later clause-folding and rule proofs
    use this to translate substituted bodies into semantic clause witnesses. *)
Lemma eval_subst_product d m s rho p :
  eval_product d m rho (subst_product s p) <->
  eval_product d m (subst_valuation m s rho) p.
Proof.
  unfold eval_product, eval_product_with, subst_product. rewrite Forall_map.
  split; intro H.
  - eapply Forall_impl; [|exact H]; intros a Ha.
    apply (proj1 (eval_subst_atom d m s rho a)); exact Ha.
  - eapply Forall_impl; [|exact H]; intros a Ha.
    apply (proj2 (eval_subst_atom d m s rho a)); exact Ha.
Qed.
