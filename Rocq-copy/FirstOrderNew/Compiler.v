From Stdlib Require Import List Bool Arith String Lia.
From CyclistRocq.FirstOrderNew Require Export Search.
From CyclistRocq.FirstOrderNew Require Import LocalRules Unfolding.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

(** Concrete native compiler. No expected label is used as proof evidence.
    Constructors below validate their own side conditions. New menus extract
    labels from the resulting certificates, rather than translating the older
    pure source layouts in RuleGeneration. *)
Definition native_axiom_application name j := {| application_name := name;
  conclusion := j; premises := [] |}.
Definition native_axiom_certificate d j (name : string) (H : axiom_check j = true)
    : certified_application d j.
Proof.
  refine {| certified_rule := native_axiom_application name j;
            certified_conclusion := eq_refl |}.
  constructor; intros w Hbad; exfalso; apply Hbad.
  apply (proj1 (valid_iff_worlds d j)), axiom_check_sound; exact H.
Defined.
Definition checked_ex_falso d j : option (certified_application d j).
Proof.
  destruct (Bool.bool_dec (contradictionb j) true) as [H|]; [|exact None].
  refine (Some (native_axiom_certificate d j "Ex Falso" _)).
  unfold axiom_check; now rewrite H.
Defined.
Definition checked_identity d j : option (certified_application d j).
Proof.
  destruct (Bool.bool_dec (identityb j) true) as [H|]; [|exact None].
  refine (Some (native_axiom_certificate d j "Id" _)).
  unfold axiom_check; rewrite H; apply orb_true_r.
Defined.

Definition native_left_binding j := match j.(antecedent) with
  | [p] => Simplification.first_some Simplification.eq_binding p
  | _ => None end.
Definition native_right_binding j := Simplification.first_some (fun ip =>
  match Simplification.first_some Simplification.ex_binding (snd ip) with
  | Some (v,t) => Some (fst ip,v,t) | None => None end) (positions j.(succedent)).
Definition native_constructor_position injective p :=
  Simplification.first_some (fun ia => match Simplification.constructor_eqs injective (snd ia) with
    | Some _ => Some (fst ia) | None => None end) (positions p).
Definition native_left_constructor_position j := match j.(antecedent) with
  | [p] => option_map (fun ai => (0,ai)) (native_constructor_position true p)
  | _ => None end.
Definition native_right_constructor_position j := Simplification.first_some (fun ip =>
  option_map (fun ai => (fst ip,ai)) (native_constructor_position false (snd ip)))
  (positions j.(succedent)).
Definition binding_matches v t binding := match binding with
  | Some (u,r) => variable_eqb v u && term_eqb t r | None => false end.
Definition indexed_binding_matches pi v t binding := match binding with
  | Some (qi,u,r) => Nat.eqb pi qi && variable_eqb v u && term_eqb t r
  | None => false end.
Definition position_matches pi ai position := match position with
  | Some (qi,bi) => Nat.eqb pi qi && Nat.eqb ai bi | None => false end.
Definition native_atom_at f pi ai := match nth_error f pi with
  | Some p => Simplification.first_some (fun u =>
      if Nat.eqb (List.length u.(Unfolding.unfold_prefix)) ai then Some u else None)
      (Unfolding.atom_descriptors p)
  | None => None end.
Definition universal_variable_termb t := match t with Var v => is_free v | _ => false end.
Definition native_binding_eq_dec (x y : variable * term) : {x = y} + {x <> y}.
Proof. decide equality; [apply term_eq_dec|apply variable_eq_dec]. Defined.
Definition native_substitution_eq_dec := list_eq_dec native_binding_eq_dec.
Definition checked_instantiation_at d j pi v t := match nth_error j.(succedent) pi with
  | Some p => if negb (is_free v) && universal_variable_termb t &&
                  existsb (variable_eqb v) (product_vars p) then
      LocalRules.checked_rhs_instantiation d j p [(v,t)]
      else None
  | None => None end.
Definition first_instantiation_product j v := Simplification.first_some (fun ip =>
  if existsb (variable_eqb v) (product_vars (snd ip)) then Some (fst ip) else None)
  (positions j.(succedent)).
Definition compile_substitution d j theta target : option (certified_application d j) :=
  match sequent_eq_dec (subst_sequent theta target) j with
  | left E => match LocalRules.checked_backward_substitution d theta target with
    | Some c => Some (LocalRules.retarget_certificate d j (subst_sequent theta target) E c)
    | None => match LocalRules.checked_backward_substitution_scoped d theta target with
      | Some c => Some (LocalRules.retarget_certificate d j (subst_sequent theta target) E c)
      | None => None end end
  | right _ => None end.
Definition compile_left_unfold_at d j pi ai tag :=
  if Nat.eqb tag (Unfolding.fresh_logical_tag j) then
    match native_atom_at j.(antecedent) pi ai with
    | Some u => Unfolding.checked_left_unfold_at d j pi u | None => None end
  else None.
Definition compile_right_unfold_at d j pi ai ci :=
  match native_atom_at j.(succedent) pi ai,nth_error d ci with
  | Some u,Some c => Unfolding.checked_right_unfold d j u c
  | _,_ => None end.
Definition compile_right_unfold_matched fuel d j pi ai ci :=
  match native_atom_at j.(succedent) pi ai,nth_error d ci with
  | Some u,Some c => Unfolding.checked_right_unfold_matched fuel d j u c
  | _,_ => None end.
Definition compile_right_unfold_instance d j pi ai ci theta :=
  match native_atom_at j.(succedent) pi ai,nth_error d ci with
  | Some u,Some c => Unfolding.checked_right_unfold_instance d j u c theta
  | _,_ => None end.
Definition compile_fold d j ci theta tag := match nth_error d ci with
  | Some c => if negb (Nat.eqb (List.length c.(body)) 0) &&
                  Nat.eqb tag (Unfolding.fresh_logical_tag j)
      then LocalRules.checked_fold d j c theta tag else None
  | None => None end.

Definition compile_rule_descriptor d j rd : option (certified_application d j) :=
  match rd with
  | RDExFalso => checked_ex_falso d j
  | RDIdentity => checked_identity d j
  | RDTrivialEqualities => LocalRules.trivial_equality_rule d j
  | RDLeftEquality v t => if binding_matches v t (native_left_binding j)
      then LocalRules.left_equality_rule d j else None
  | RDRightEquality pi v t => if indexed_binding_matches pi v t (native_right_binding j)
      then LocalRules.right_equality_rule d j else None
  | RDDischargeRight => LocalRules.right_discharge_rule d j
  | RDLeftInjective pi ai => if position_matches pi ai (native_left_constructor_position j)
      then LocalRules.left_injectivity_rule d j else None
  | RDRightCongruence pi ai => if position_matches pi ai (native_right_constructor_position j)
      then LocalRules.right_congruence_rule d j else None
  | RDLeftDisjunction => if 2 <=? List.length j.(antecedent)
      then Some (LocalRules.left_disjunction d j) else None
  | RDInstantiate v t => match first_instantiation_product j v with
    | Some pi => checked_instantiation_at d j pi v t | None => None end
  | RDRightConjunction => LocalRules.checked_right_split d j 1
  | RDRightUnfold pi ai ci => compile_right_unfold_at d j pi ai ci
  | RDLeftUnfold ai tag => match j.(antecedent) with
    | [_] => compile_left_unfold_at d j 0 ai tag | _ => None end
  | RDFold ci theta tag => compile_fold d j ci theta tag
  | RDWeaken target => LocalRules.checked_weakening d j target
  | RDSubstitute theta target => compile_substitution d j theta target
  | RDInstantiateAt pi v t => checked_instantiation_at d j pi v t
  | RDRightSplit n => LocalRules.checked_right_split d j n
  | RDLeftUnfoldAt pi ai tag => compile_left_unfold_at d j pi ai tag
  | RDRightUnfoldMatched fuel pi ai ci => compile_right_unfold_matched fuel d j pi ai ci
  | RDRightUnfoldInstance pi ai ci theta => compile_right_unfold_instance d j pi ai ci theta
  end.

Definition proposal_from_certificate d j rd (c : certified_application d j) :=
  propose rd j (map premise_label (certified_rule d j c).(premises)).
Definition compiled_proposal d j rd := match compile_rule_descriptor d j rd with
  | Some c => Some (proposal_from_certificate d j rd c) | None => None end.
Definition proposal_changedb p := existsb
  (fun k => negb (sequent_eqb p.(proposal_conclusion) k)) p.(proposal_premises).
Definition compiled_changed_proposal d j rd := match compiled_proposal d j rd with
  | Some p => if proposal_changedb p then Some p else None | None => None end.
Definition compiled_axiom_proposals d j := match compiled_proposal d j RDExFalso with
  | Some p => [p]
  | None => RuleGeneration.option_list (compiled_proposal d j RDIdentity) end.
Definition native_simplification_descriptors j :=
  [Some RDTrivialEqualities;
   option_map (fun vt => RDLeftEquality (fst vt) (snd vt)) (native_left_binding j);
   option_map (fun ivt => let '(pi,v,t) := ivt in RDRightEquality pi v t) (native_right_binding j);
   Some RDDischargeRight;
   option_map (fun ia => RDLeftInjective (fst ia) (snd ia)) (native_left_constructor_position j);
   option_map (fun ia => RDRightCongruence (fst ia) (snd ia)) (native_right_constructor_position j)].
Definition compiled_simplification_proposals d j := flat_map (fun o => match o with
  | Some rd => RuleGeneration.option_list (compiled_changed_proposal d j rd)
  | None => [] end) (native_simplification_descriptors j).
Definition compiled_simplification_proposal d j := first_available (fun o => match o with
  | Some rd => compiled_changed_proposal d j rd | None => None end)
  (native_simplification_descriptors j).
Definition compiled_left_split_proposals d j :=
  RuleGeneration.option_list (compiled_proposal d j RDLeftDisjunction).
Definition compiled_instantiation_proposals limits d j :=
  let us := filter is_free (existing_variables j) in
  bounded_bind limits.(candidate_limit) (fun ip =>
    bounded_bind limits.(candidate_limit) (fun v =>
      bounded_bind limits.(candidate_limit) (fun u =>
        RuleGeneration.option_list (compiled_changed_proposal d j
          (RDInstantiateAt (fst ip) v (Var u)))) us)
      (existential_variables (product_vars (snd ip)))) (positions j.(succedent)).
Definition compiled_right_split_proposals limits d j := match j.(succedent) with
  | [p] => bounded_bind limits.(candidate_limit) (fun n =>
      RuleGeneration.option_list (compiled_proposal d j (RDRightSplit n)))
      (seq 1 (List.length p - 1))
  | _ => [] end.
Definition compiled_left_unfold_proposals limits d j :=
  bounded_bind limits.(candidate_limit) (fun ip =>
    bounded_bind limits.(candidate_limit) (fun u => RuleGeneration.option_list
      (compiled_proposal d j (RDLeftUnfoldAt (fst ip)
        (List.length u.(Unfolding.unfold_prefix)) (Unfolding.fresh_logical_tag j))))
      (Unfolding.atom_descriptors (snd ip))) (positions j.(antecedent)).

(** Native freshening preserves prime variables. Unmatched fresh Free clause
    locals must additionally be turned into fresh Exist witnesses on the RHS.
    This is an arbitrary instance of the SAME checked native schema: all head
    equalities are retained, and the goal/context are never substituted. *)
Definition complete_right_scope j c theta :=
  let fresh := Unfolding.right_clause (Unfolding.unfolding_start j) c in
  let unmatched := filter (fun v => is_free v &&
    match binding theta v with None => true | Some _ => false end)
    (nodup variable_eq_dec (clause_vars fresh)) in
  let avoid := sequent_vars j ++ clause_vars fresh ++
               List.concat (map (fun xt => term_vars (snd xt)) theta) in
  theta ++ combine unmatched (map (fun n => Var (Exist n))
    (seq (fresh_id avoid) (List.length unmatched))).
Definition native_right_descriptor limits j pi u ci c :=
  match Unfolding.right_unfold_matched_substitution limits.(matching_fuel) j u c with
  | None => None
  | Some theta =>
    let completed := complete_right_scope j c theta in
    let ai := List.length u.(Unfolding.unfold_prefix) in
    if eqb_of_dec native_substitution_eq_dec theta completed
    then Some (RDRightUnfoldMatched limits.(matching_fuel) pi ai ci)
    else Some (RDRightUnfoldInstance pi ai ci completed)
  end.
Definition compiled_right_unfold_proposals limits d j :=
  bounded_bind limits.(candidate_limit) (fun ic =>
    bounded_bind limits.(candidate_limit) (fun ip =>
      bounded_bind limits.(candidate_limit) (fun u =>
        match native_right_descriptor limits j (fst ip) u (fst ic) (snd ic) with
        | Some rd => RuleGeneration.option_list (compiled_proposal d j rd)
        | None => [] end) (Unfolding.atom_descriptors (snd ip)))
      (positions j.(succedent))) (positions d).
(** Keep source optimized candidates first. The native equation schema also
    supports a symbolic RHS argument which cannot directionally match a clause
    head (notably [P(x')] with a constant base head). Such remaining cases are
    checked instances, with all fresh Free clause variables scoped as witnesses;
    their full head equations are sufficient evidence independently of matching.
    No failed or unverified matcher result is treated as a substitution proof. *)
Definition compiled_right_fallback_proposals limits d j :=
  bounded_bind limits.(candidate_limit) (fun ic =>
    bounded_bind limits.(candidate_limit) (fun ip =>
      bounded_bind limits.(candidate_limit) (fun u =>
        match Unfolding.right_unfold_matched_substitution limits.(matching_fuel) j u (snd ic) with
        | Some _ => []
        | None => RuleGeneration.option_list (compiled_proposal d j
            (RDRightUnfoldInstance (fst ip) (List.length u.(Unfolding.unfold_prefix)) (fst ic)
              (complete_right_scope j (snd ic) []))) end)
        (Unfolding.atom_descriptors (snd ip))) (positions j.(succedent))) (positions d).
Definition compiled_right_family_proposals limits d j :=
  firstn limits.(candidate_limit)
    (compiled_right_unfold_proposals limits d j ++ compiled_right_fallback_proposals limits d j).
Definition compiled_fold_proposals limits d j := match j.(antecedent) with
  | [p] => bounded_bind limits.(candidate_limit) (fun ic =>
    if Nat.eqb (List.length (snd ic).(body)) 0 then [] else
    bounded_bind limits.(candidate_limit) (fun theta => RuleGeneration.option_list
      (compiled_proposal d j (RDFold (fst ic) theta (Unfolding.fresh_logical_tag j))))
      (bounded_match_product limits.(candidate_limit) limits.(matching_fuel)
        [] (snd ic).(body) p)) (positions d)
  | _ => [] end.

Definition proposal_compilableb d p :=
  match compile_rule_descriptor d p.(proposal_conclusion) p.(proposal_descriptor) with
  | Some c => application_matches p (certified_rule d p.(proposal_conclusion) c)
  | None => false end.
(** Drop identity bindings before native substitution checks. A genuine prime
    renaming uses the scoped native API, which reserves unmapped prime images
    and checks injectivity over the ENTIRE companion scope. *)
Definition remove_identity_bindings theta := filter
  (fun xt => negb (term_eqb (Var (fst xt)) (snd xt))) theta.
Fixpoint backlink_preparation_check d label steps target := match steps with
  | [] => sequent_eqb label target
  | p::rest => sequent_eqb label p.(proposal_conclusion) && proposal_compilableb d p &&
      match p.(proposal_premises) with
      | [k] => backlink_preparation_check d k rest target | _ => false end end.
Definition backlink_compilableb d b :=
  backlink_preparation_check d b.(backlink_source) b.(backlink_preparation)
                              b.(backlink_target) &&
  exact_backlink_edgeb b.(backlink_target) b.(backlink_exact_edge).
Definition recertify_backlink_plan d b :=
  match make_backlink_plan b.(backlink_source) b.(backlink_target_index)
      b.(backlink_target) (remove_identity_bindings b.(backlink_substitution)) with
  | Some b' => if backlink_compilableb d b' then Some b' else None
  | None => None end.
Definition compiled_backlink_plans limits d idx j nodes :=
  bounded_bind limits.(candidate_limit) (fun b => RuleGeneration.option_list
    (recertify_backlink_plan d b)) (backlink_plans limits idx j nodes).
Definition compiled_backlink_plans_all limits d j nodes :=
  bounded_bind limits.(candidate_limit) (fun b => RuleGeneration.option_list
    (recertify_backlink_plan d b)) (backlink_plans_all limits j nodes).

Definition compiled_terminal_program d j := match compiled_axiom_proposals d j with
  | p::_ => primitive_program p | [] => ProgramOpen j end.
Fixpoint compiled_normalize_program fuel d j :=
  match compiled_simplification_proposal d j with
  | None => compiled_terminal_program d j
  | Some p => match fuel with
    | 0 => ProgramOpen j
    | S fuel' => ProgramApply p
        (map (compiled_normalize_program fuel' d) p.(proposal_premises)) end end.
Definition compiled_wrapped_program limits d p := ProgramApply p
  (map (compiled_normalize_program limits.(simplification_steps) d) p.(proposal_premises)).
Definition compiled_combined_unfold_programs limits d j :=
  bounded_bind limits.(combination_limit) (fun p =>
    bind_program limits.(combination_limit) (fun k =>
      match compiled_simplification_proposal d k with
      | Some _ => []
      | None => map (compiled_wrapped_program limits d)
          (compiled_right_family_proposals limits d k) end)
      (compiled_wrapped_program limits d p)) (compiled_left_unfold_proposals limits d j).
Definition compiled_fold_backlink_programs limits d j nodes :=
  bounded_bind limits.(combination_limit) (fun p =>
    bind_program limits.(combination_limit) (fun k => map ProgramBacklink
      (compiled_backlink_plans_all limits d k nodes)) (primitive_program p))
    (compiled_fold_proposals limits d j).
Definition compiled_choice_programs limits d idx j nodes :=
  map ProgramBacklink (compiled_backlink_plans limits d idx j nodes) ++
  map (compiled_wrapped_program limits d) (compiled_left_split_proposals d j) ++
  map (compiled_wrapped_program limits d) (compiled_instantiation_proposals limits d j) ++
  map (compiled_wrapped_program limits d) (compiled_right_split_proposals limits d j) ++
  map (compiled_wrapped_program limits d) (compiled_right_family_proposals limits d j) ++
  compiled_combined_unfold_programs limits d j ++
  map (compiled_wrapped_program limits d) (compiled_left_unfold_proposals limits d j) ++
  compiled_fold_backlink_programs limits d j nodes.
Definition native_source_menu limits d idx j nodes :=
  match compiled_axiom_proposals d j with
  | p::ps => {| menu_axioms := map primitive_program (p::ps);
               menu_simplifications := []; menu_choices := [] |}
  | [] => match compiled_simplification_proposal d j with
    | Some p => {| menu_axioms := []; menu_simplifications := [compiled_wrapped_program limits d p];
                  menu_choices := [] |}
    | None => {| menu_axioms := []; menu_simplifications := [];
                 menu_choices := compiled_choice_programs limits d idx j nodes |}
    end end.

Fixpoint program_proposals program := match program with
  | ProgramOpen _ => []
  | ProgramApply p children => p :: List.concat (map program_proposals children)
  | ProgramBacklink b => b.(backlink_preparation) end.
Definition program_compilableb d program := forallb (proposal_compilableb d)
  (program_proposals program).
Definition filter_compiled_menu d menu :=
  {| menu_axioms := filter (program_compilableb d) menu.(menu_axioms);
     menu_simplifications := filter (program_compilableb d) menu.(menu_simplifications);
     menu_choices := filter (program_compilableb d) menu.(menu_choices) |}.
(** Public integration entry point. Every ProgramApply and every backlink
    preparation is recompiled and checked for EXACT native premise agreement. *)
Definition compiled_source_menu limits d idx j nodes : rule_menu :=
  filter_compiled_menu d (native_source_menu limits d idx j nodes).
Definition certified_rule_menu := compiled_source_menu.

Lemma proposal_from_certificate_matches d j rd c :
  application_matches (proposal_from_certificate d j rd c) (certified_rule d j c) = true.
Proof.
  unfold application_matches, proposal_from_certificate, propose; cbn.
  rewrite (certified_conclusion d j c).
  apply andb_true_iff; split; [apply sequent_eqb_spec|apply eqb_of_dec_spec]; reflexivity.
Qed.
Theorem compiled_proposal_recompiles d j rd p : compiled_proposal d j rd = Some p ->
  exists c, compile_rule_descriptor d p.(proposal_conclusion) p.(proposal_descriptor) = Some c /\
    application_matches p (certified_rule d p.(proposal_conclusion) c) = true.
Proof.
  unfold compiled_proposal; destruct (compile_rule_descriptor d j rd) as [c|] eqn:E;
    [|discriminate]. intro H; inversion H; subst p; exists c; split;
    [exact E|apply proposal_from_certificate_matches].
Qed.
Lemma proposal_compilableb_spec d p : proposal_compilableb d p = true ->
  exists c, compile_rule_descriptor d p.(proposal_conclusion) p.(proposal_descriptor) = Some c /\
    application_matches p (certified_rule d p.(proposal_conclusion) c) = true.
Proof.
  unfold proposal_compilableb.
  destruct (compile_rule_descriptor d (proposal_conclusion p) (proposal_descriptor p)) as [c|] eqn:E;
    [intros H; exists c; auto|discriminate].
Qed.
Theorem compiled_source_menu_recompiles limits d idx j nodes program p :
  let menu := compiled_source_menu limits d idx j nodes in
  In program (menu.(menu_axioms) ++ menu.(menu_simplifications) ++ menu.(menu_choices)) ->
  In p (program_proposals program) ->
  exists c, compile_rule_descriptor d p.(proposal_conclusion) p.(proposal_descriptor) = Some c /\
    application_matches p (certified_rule d p.(proposal_conclusion) c) = true.
Proof.
  cbn zeta; unfold compiled_source_menu, filter_compiled_menu; cbn.
  intros Hprogram Hp; repeat rewrite in_app_iff in Hprogram.
  assert (program_compilableb d program = true) as Hcheck.
  { destruct Hprogram as [H|[H|H]]; apply filter_In in H; tauto. }
  unfold program_compilableb in Hcheck; apply forallb_forall with (x := p) in Hcheck;
    [now apply proposal_compilableb_spec|exact Hp].
Qed.
Theorem compiled_proposal_local_sound d p c :
  compile_rule_descriptor d p.(proposal_conclusion) p.(proposal_descriptor) = Some c ->
  application_matches p (certified_rule d p.(proposal_conclusion) c) = true ->
  (forall k, In k p.(proposal_premises) -> valid d k) -> valid d p.(proposal_conclusion).
Proof.
  intros _ Hmatch Hvalid; apply application_matches_spec in Hmatch.
  destruct Hmatch as [_ Hps]. apply LocalRules.certified_local_sound with (c := c).
  intros premise Hin; apply Hvalid; rewrite Hps; apply in_map; exact Hin.
Qed.
