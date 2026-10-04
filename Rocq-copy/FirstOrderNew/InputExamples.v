From Stdlib Require Import List Bool String ZArith.
From CyclistRocq.FirstOrderNew Require Import Input SourceDefinitions.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(** The nine actual [benchmarks/fo/*.tst] goals, in filename order. These
    assertions check the complete AST, not merely a parser-success flag. *)
Definition benchmark_goal_texts : list string := [
  "O(x) |- N(x)";
  "E(x) \/ O(x) |- N(x)";
  "N(x) |- O(x) \/ E(x)";
  "N(x) & N(y) |- Q(x,y)";
  "N(x) |- ADD(x,0,x)";
  "N(x) & N(y) & ADD(x,y,z) |- N(z)";
  "N(x) & N(y) & ADD(x,y,z) |- ADD(x,s(y),s(z))";
  "N(y) & N(x) |- H(x, y)";
  "N(y) & N(x) |- N2(x,y)"].
Definition expected_benchmark_sequents : list sequent := [
  {| antecedent := [[Pred 0 "O" [x]]]; succedent := [[Pred 1 "N" [x]]] |};
  {| antecedent := [[Pred 0 "E" [x]]; [Pred 1 "O" [x]]];
     succedent := [[Pred 2 "N" [x]]] |};
  {| antecedent := [[Pred 0 "N" [x]]];
     succedent := [[Pred 1 "O" [x]]; [Pred 2 "E" [x]]] |};
  {| antecedent := [[Pred 0 "N" [x]; Pred 1 "N" [y]]];
     succedent := [[Pred 2 "Q" [x; y]]] |};
  {| antecedent := [[Pred 0 "N" [x]]];
     succedent := [[Pred 1 "ADD" [x; zero; x]]] |};
  {| antecedent := [[Pred 0 "N" [x]; Pred 1 "N" [y]; Pred 2 "ADD" [x; y; z]]];
     succedent := [[Pred 3 "N" [z]]] |};
  {| antecedent := [[Pred 0 "N" [x]; Pred 1 "N" [y]; Pred 2 "ADD" [x; y; z]]];
     succedent := [[Pred 3 "ADD" [x; successor y; successor z]]] |};
  (* In these two source goals [y] is encountered first: it receives id 0. *)
  {| antecedent := [[Pred 0 "N" [x]; Pred 1 "N" [y]]];
     succedent := [[Pred 2 "H" [y; x]]] |};
  {| antecedent := [[Pred 0 "N" [x]; Pred 1 "N" [y]]];
     succedent := [[Pred 2 "N2" [y; x]]] |}].

Example all_nine_source_goals_parse_exactly :
  map (parse_sequent closed_source_definitions) benchmark_goal_texts =
  map (@Ok sequent) expected_benchmark_sequents.
Proof. vm_compute; reflexivity. Qed.
Example all_nine_source_goals_are_validated :
  forallb (fun text => match parse_sequent closed_source_definitions text with
    | Ok j => sequent_wfb closed_source_definitions j
    | Error _ => false end) benchmark_goal_texts = true.
Proof. vm_compute; reflexivity. Qed.

Example nested_term_variable_classes_and_stability :
  parse_term "cons(x,cons(y',x))" =
  Ok (cons (Var (Free 0)) (cons (Var (Exist 1)) (Var (Free 0)))).
Proof. vm_compute; reflexivity. Qed.
Example nested_term_variables_are_recursively_collected :
  match parse_term "cons(x,cons(y',x))" with
  | Ok t => term_vars t | Error _ => [] end = [Free 0; Exist 1; Free 0].
Proof. vm_compute; reflexivity. Qed.
Example same_identifier_is_stable_across_the_goal :
  parse_sequent closed_source_definitions
    "LIST(cons(x,cons(y,x))) |- LIST(cons(x,cons(y,z')))" =
  Ok {| antecedent := [[Pred 0 "LIST" [cons x (cons y x)]]];
        succedent := [[Pred 1 "LIST" [cons x (cons y (Var (Exist 2)))]]] |}.
Proof. vm_compute; reflexivity. Qed.
Example nested_predicate_variables_are_recursively_collected :
  match parse_sequent_raw
    "LIST(cons(x,cons(y,x))) |- LIST(cons(x,cons(y,z')))" with
  | Ok j => sequent_vars j | Error _ => [] end =
  [Free 0; Free 1; Free 0; Free 0; Free 1; Exist 2].
Proof. vm_compute; reflexivity. Qed.
Example primed_and_unprimed_names_are_distinct :
  parse_sequent_raw "x=x' |- x'=x" =
  Ok {| antecedent := [[Eq x (Var (Exist 1))]];
        succedent := [[Eq (Var (Exist 1)) x]] |}.
Proof. vm_compute; reflexivity. Qed.
Example underscore_is_stable_too :
  parse_sequent [] "f(_,_) = _ |- true" =
  Ok {| antecedent := [[Eq (Fun "f" [x; x]) x]]; succedent := [[]] |}.
Proof. vm_compute; reflexivity. Qed.

Example disequality_is_not_equality :
  parse_atom "x!=w" = Ok (Deq x y).
Proof. vm_compute; reflexivity. Qed.
Example function_headed_equality_is_not_a_predicate :
  parse_atom "s(x)=s(y)" = Ok (Eq (successor x) (successor y)).
Proof. vm_compute; reflexivity. Qed.
Example function_headed_disequality_is_not_a_predicate :
  parse_atom "cons(x,x)!=cons(y,y)" = Ok (Deq (cons x x) (cons y y)).
Proof. vm_compute; reflexivity. Qed.
Example equality_does_not_allocate_a_predicate_tag :
  parse_sequent closed_source_definitions "s(x)=s(y) & N(x) |- N(y)" =
  Ok {| antecedent := [[Eq (successor x) (successor y); Pred 0 "N" [x]]];
        succedent := [[Pred 1 "N" [y]]] |}.
Proof. vm_compute; reflexivity. Qed.
Example negative_integer_and_nested_function :
  parse_term "f(-12,s(+3))" =
  Ok (Fun "f" [Const (-12)%Z; successor (Const 3%Z)]).
Proof. vm_compute; reflexivity. Qed.
Example integers_use_Z_not_host_machine_integers :
  parse_term "-123456789012345678901234567890" =
  Ok (Const (-123456789012345678901234567890)%Z).
Proof. vm_compute; reflexivity. Qed.
Example true_is_the_empty_product : parse_product "true" = Ok [].
Proof. vm_compute; reflexivity. Qed.
Example products_and_dnf_preserve_source_order :
  parse_formula "x!=0 & N(x) \/ true \/ N(s(x))" =
  Ok [[Deq x zero; Pred 0 "N" [x]]; []; [Pred 1 "N" [successor x]]].
Proof. vm_compute; reflexivity. Qed.

Example antecedent_primed_variable_is_rejected :
  parse_sequent closed_source_definitions "N(x') |- N(x')" =
  Error (AntecedentExistential (Exist 0)).
Proof. vm_compute; reflexivity. Qed.
Example deeply_nested_antecedent_primed_variable_is_rejected :
  parse_sequent closed_source_definitions "N(s(cons(0,x'))) |- true" =
  Error (AntecedentExistential (Exist 0)).
Proof. vm_compute; reflexivity. Qed.
Example primed_variable_in_antecedent_equality_is_rejected :
  parse_sequent [] "f(s(x'))=0 |- true" =
  Error (AntecedentExistential (Exist 0)).
Proof. vm_compute; reflexivity. Qed.
Example primed_variable_in_a_later_antecedent_disjunct_is_rejected :
  parse_sequent closed_source_definitions "N(x) \/ N(s(y')) |- true" =
  Error (AntecedentExistential (Exist 1)).
Proof. vm_compute; reflexivity. Qed.
Example right_primed_variable_is_allowed_and_preserved :
  parse_sequent closed_source_definitions "N(x) |- N(s(y'))" =
  Ok {| antecedent := [[Pred 0 "N" [x]]];
        succedent := [[Pred 1 "N" [successor (Var (Exist 1))]]] |}.
Proof. vm_compute; reflexivity. Qed.
Example repeated_right_primed_spelling_in_different_products :
  parse_sequent closed_source_definitions "true |- N(x') \/ N(s(x'))" =
  Ok {| antecedent := [[]];
        succedent := [[Pred 0 "N" [Var (Exist 0)]];
                      [Pred 1 "N" [successor (Var (Exist 0))]]] |}.
Proof. vm_compute; reflexivity. Qed.

Example undefined_goal_predicate_has_a_named_diagnostic :
  parse_sequent closed_source_definitions "N(x) |- ADD_2(x,x,x)" =
  Error (UndefinedPredicate "ADD_2").
Proof. vm_compute; reflexivity. Qed.
Example incorrect_goal_predicate_arity_is_diagnosed :
  parse_sequent closed_source_definitions "N(x,y) |- true" =
  Error (PredicateArityMismatch "N" [1] 2).
Proof. vm_compute; reflexivity. Qed.
Example incorrect_nested_constructor_arity_is_diagnosed :
  parse_sequent closed_source_definitions "true |- LIST(cons(x))" =
  Error (FunctionArityMismatch "cons" 2 1).
Proof. vm_compute; reflexivity. Qed.
Example incorrect_constructor_in_equality_is_diagnosed :
  parse_sequent [] "s(x,y)=z |- true" =
  Error (FunctionArityMismatch "s" 1 2).
Proof. vm_compute; reflexivity. Qed.
Example invalid_supplied_signature_is_also_rejected :
  parse_sequent source_definitions "N(x) |- N(x)" =
  Error (UndefinedPredicate "ADD_2").
Proof. vm_compute; reflexivity. Qed.
Example undefined_raw_goal_remains_inspectable :
  parse_sequent_raw "true |- ADD_2(x,x,x)" =
  Ok {| antecedent := [[]]; succedent := [[Pred 0 "ADD_2" [x; x; x]]] |}.
Proof. vm_compute; reflexivity. Qed.

Example definition_header_head_mismatch_is_not_silently_ignored :
  parse_definitions "N { true => N(0) | N(x) => M(s(x)) }" =
  Error (HeaderHeadMismatch "N" "M").
Proof. vm_compute; reflexivity. Qed.
Example raw_definitions_also_check_header_agreement :
  parse_definitions_raw "N { true => M(0) }" =
  Error (HeaderHeadMismatch "N" "M").
Proof. vm_compute; reflexivity. Qed.
Example function_equality_in_positive_clause_body :
  parse_definitions "N { s(x)=s(y) & N(x) => N(s(y)) }" =
  Ok [mk_clause "N" [successor y]
        [Eq (successor x) (successor y); Pred 0 "N" [x]]].
Proof. vm_compute; reflexivity. Qed.
Example forward_and_mutual_predicate_references_are_validated_after_parsing :
  parse_definitions "E { O(x) => E(s(x)) }; O { E(x) => O(s(x)) }" =
  Ok [mk_clause "E" [successor x] [Pred 0 "O" [x]];
      mk_clause "O" [successor x] [Pred 1 "E" [x]]].
Proof. vm_compute; reflexivity. Qed.
Example trailing_definition_semicolon_is_accepted :
  parse_definitions "N { true => N(0) | N(x) => N(s(x)) };" =
  Ok [mk_clause "N" [zero] []; mk_clause "N" [successor x] [Pred 0 "N" [x]]].
Proof. vm_compute; reflexivity. Qed.
Example inconsistent_definition_head_arities_are_diagnosed :
  parse_definitions "N { true => N(0) | true => N(x,y) }" =
  Error (InconsistentDefinitionArity "N" 1 2).
Proof. vm_compute; reflexivity. Qed.
Example wrong_definition_body_reference_arity_is_diagnosed :
  parse_definitions "P { Q(x,y) => P(x) }; Q { true => Q(0) }" =
  Error (PredicateArityMismatch "Q" [1] 2).
Proof. vm_compute; reflexivity. Qed.
Example wrong_definition_head_constructor_arity_is_diagnosed :
  parse_definitions "N { true => N(s(x,y)) }" =
  Error (FunctionArityMismatch "s" 1 2).
Proof. vm_compute; reflexivity. Qed.
Example primed_clause_variables_are_not_antecedent_goal_variables :
  parse_definitions "N { N(x') => N(s(x')) }" =
  Ok [mk_clause "N" [successor (Var (Exist 0))] [Pred 0 "N" [Var (Exist 0)]]].
Proof. vm_compute; reflexivity. Qed.

Example late_explicit_numeric_tag_is_reserved_before_implicit_tags :
  parse_sequent closed_source_definitions "N(x) & N[0](x) |- N(x)" =
  Ok {| antecedent := [[Pred 1 "N" [x]; Pred 0 "N" [x]]];
        succedent := [[Pred 2 "N" [x]]] |}.
Proof. vm_compute; reflexivity. Qed.
Example repeated_explicit_numeric_tag_is_preserved :
  parse_sequent closed_source_definitions "N[7](x) |- N[7](x)" =
  Ok {| antecedent := [[Pred 7 "N" [x]]]; succedent := [[Pred 7 "N" [x]]] |}.
Proof. vm_compute; reflexivity. Qed.
Example symbolic_tags_are_stable_and_implicit_tags_are_fresh :
  parse_sequent closed_source_definitions
    "N[a](x) & N(x) |- N[a](x) & N[b'](x)" =
  Ok {| antecedent := [[Pred 0 "N" [x]; Pred 2 "N" [x]]];
        succedent := [[Pred 0 "N" [x]; Pred 1 "N" [x]]] |}.
Proof. vm_compute; reflexivity. Qed.
Example numeric_and_symbolic_explicit_tags_do_not_collide :
  parse_sequent closed_source_definitions "N[a](x) & N[7](x) |- N(x)" =
  Ok {| antecedent := [[Pred 8 "N" [x]; Pred 7 "N" [x]]];
        succedent := [[Pred 9 "N" [x]]] |}.
Proof. vm_compute; reflexivity. Qed.
Example apostrophe_distinguishes_symbolic_tag_names :
  parse_sequent closed_source_definitions "N[a](x) |- N[a'](x)" =
  Ok {| antecedent := [[Pred 0 "N" [x]]]; succedent := [[Pred 1 "N" [x]]] |}.
Proof. vm_compute; reflexivity. Qed.
Example negative_tags_are_rejected :
  parse_atom "N[-1](x)" = Error (SyntaxError 2 "a nonnegative tag").
Proof. vm_compute; reflexivity. Qed.

Example suffix_after_a_goal_is_not_ignored :
  parse_sequent_raw "N(x) |- N(x) junk" = Error (SyntaxError 13 "end of input").
Proof. vm_compute; reflexivity. Qed.
Example missing_parenthesis_has_an_EOF_offset :
  parse_atom "N(s(x)" = Error (SyntaxError 6 ", or )").
Proof. vm_compute; reflexivity. Qed.
Example missing_definition_separator_is_rejected :
  match parse_definitions_raw
    "N { true => N(0) } N2 { true => N2(0,0) }" with
  | Error (SyntaxError _ "end of input") => true | _ => false end = true.
Proof. vm_compute; reflexivity. Qed.
Example disjunctive_clause_body_is_not_a_positive_product :
  match parse_definitions_raw "N { N(x) \/ N(y) => N(s(x)) }" with
  | Error (SyntaxError _ "=>") => true | _ => false end = true.
Proof. vm_compute; reflexivity. Qed.
Example empty_application_is_not_supported_by_the_source_grammar :
  parse_term "f()" = Error (SyntaxError 2 "a term").
Proof. vm_compute; reflexivity. Qed.
Example empty_formula_is_not_accepted_as_false :
  parse_formula "" = Error (SyntaxError 0 "true or a nonempty product").
Proof. vm_compute; reflexivity. Qed.
Example empty_definitions_are_not_silently_accepted :
  parse_definitions "" = Error (SyntaxError 0 "an identifier").
Proof. vm_compute; reflexivity. Qed.
Example malformed_lexical_token_reports_its_original_offset :
  parse_term "  @" = Error (SyntaxError 2 "a first-order input token").
Proof. vm_compute; reflexivity. Qed.
Example budget_exhaustion_is_distinct_from_success_or_invalidity :
  parse_sequent_raw_with_fuel 3 "N(x)|-N(x)" = Error (FuelExhausted 3).
Proof. vm_compute; reflexivity. Qed.
Example checked_entrypoints_also_expose_budget_exhaustion :
  parse_sequent_with_fuel closed_source_definitions 0 "N(x)|-N(x)" =
  Error (FuelExhausted 0).
Proof. vm_compute; reflexivity. Qed.
Example readable_undefined_diagnostic :
  diagnostic_message (UndefinedPredicate "ADD_2") = "undefined predicate: ADD_2".
Proof. vm_compute; reflexivity. Qed.
Example readable_arity_and_position_diagnostics :
  (diagnostic_message (PredicateArityMismatch "N" [1] 2),
   diagnostic_message (SyntaxError 13 "end of input")) =
  ("predicate N: expected arity 1, got 2", "at offset 13: expected end of input").
Proof. vm_compute; reflexivity. Qed.

(** Literal [examples/fo.defs], including its unresolved [ADD_2] reference.
    [SourceDefinitions] remains the authoritative pre-existing AST transcript.
    We compare every parsed clause with that transcript after erasing only tags.
    This checks source order, all terms/variables, and the corrected COUNT guard. *)
Definition source_definition_text : string := "N { 
	true => N(0) | 
	N(x) => N(s(x)) 
} ;

N2 {
	N(y) => N2(0,y) |
	N2(y,x) => N2(s(x),y)
} ;

E {
	true => E(0) |
	O(x) => E(s(x))
} ;

O {
	E(x) => O(s(x))
} ;

P {
	true => P(0) |
	P(x) & Q(x, s(x)) => P(s(x)) 
} ;

Q {
	true => Q(x,0) |
	Q(x,y) & P(x) => Q(x,s(y))
} ;

LIST {
  true => LIST(0) |
  LIST(x) => LIST(cons(y,x))
} ;

APP {
  true => APP(0,x,x) |
  APP(x,y,z) => APP(cons(w,x), y, cons(w,z))
} ;

TAKE {
  true => TAKE(x, 0, 0) |
  true => TAKE(0, x, 0) |
  TAKE(x,y,z) => TAKE(s(x), cons(w,y), cons(w,z))
} ;

DROP {
  true => DROP(x, 0, 0) |
  true => DROP(0, x, x) |
  DROP(x,y,z) => DROP(s(x), cons(w,y), z)
} ;

MINUS {
  true => MINUS(0,x,0) |
  true => MINUS(x,0,x) |
  MINUS(x,y,z) => MINUS(s(x),s(y),z)
} ;

LEN {
	true => LEN(0,0) |
	LEN(x,y) => LEN(cons(z,x),s(y))
} ;

PLUS {
	true => PLUS(0,x,x) |
	PLUS(x,y,z) => PLUS(s(x),y,s(z))
} ;

COUNT {
	true => COUNT(x,0,0) |
	COUNT(x,y,z) => COUNT(x, cons(x,y), s(z)) |
  x!=w & COUNT(x,y,z) => COUNT(x, cons(w,y), z)
} ; 

ADD {
  N(x) => ADD(0,x,x) |
  ADD(x,y,z) => ADD(s(x), y, s(z))
} ;

MUL {
  N(x) => MUL(0,x,0) |
  MUL(x,y,z) & ADD_2(x,z,w) => MUL(s(x),y,w)
} ;

LEQ {
	true => LEQ(0,x) |
	LEQ(x,y) => LEQ(s(x),s(y))
} ;

R {
	true => R(0,x) |
	R(x,0) => R(s(x),0) |
	R(s(s(x)),y) => R(s(x),s(y))
} ;

H {
	true => H(0,0) |
	true => H(s(0),0) |
	true => H(x,s(0)) |
	H(x,y) => H(s(x),s(s(y))) |
	H(s(y),y) => H(0,s(s(y))) |
	H(s(x),x) => H(s(s(x)),0) 
}
".
Definition erase_definition_tags (ds : definitions) := map
  (fun c => {| clause_name := c.(clause_name); head := c.(head);
               body := map erase_tag c.(body) |}) ds.
Definition parsed_literal_source := parse_definitions_raw source_definition_text.

Example full_literal_transcript_has_46_clauses :
  match parsed_literal_source with Ok ds => List.length ds | Error _ => 0 end = 46.
Proof. vm_compute; reflexivity. Qed.
Example full_literal_transcript_matches_existing_source_AST :
  match parsed_literal_source with Ok ds => erase_definition_tags ds | Error _ => [] end =
  source_definitions.
Proof. vm_compute; reflexivity. Qed.
Example full_literal_transcript_preserves_the_undefined_reference :
  match parsed_literal_source with Ok ds => definition_errors ds | Error _ => [] end =
  ["ADD_2"].
Proof. vm_compute; reflexivity. Qed.
Example full_literal_checked_parse_diagnoses_ADD_2 :
  parse_definitions source_definition_text = Error (UndefinedPredicate "ADD_2").
Proof. vm_compute; reflexivity. Qed.
Example literal_COUNT_guard_is_disequality :
  match parsed_literal_source with
  | Ok ds => map body (clauses_for (erase_definition_tags ds) "COUNT")
  | Error _ => [] end =
  [[]; [Pred 0 "COUNT" [x; y; z]]; [Deq x w; Pred 0 "COUNT" [x; y; z]]].
Proof. vm_compute; reflexivity. Qed.

(** An explicitly selected closed subset; the raw source itself is not changed.
    Removing the two MUL clauses reproduces the existing closed source library. *)
Definition parsed_closed_subset : result definitions :=
  match parsed_literal_source with
  | Ok ds => validate_definitions
      (filter (fun c => negb (String.eqb c.(clause_name) "MUL")) ds)
  | Error e => Error e end.
Example parsed_closed_subset_has_exactly_the_existing_closed_AST :
  match parsed_closed_subset with Ok ds => erase_definition_tags ds | Error _ => [] end =
  closed_source_definitions.
Proof. vm_compute; reflexivity. Qed.
Example parsed_closed_subset_has_44_validated_clauses :
  match parsed_closed_subset with
  | Ok ds => Nat.eqb (List.length ds) 44 && definitions_wfb ds
  | Error _ => false end = true.
Proof. vm_compute; reflexivity. Qed.
Example all_source_goals_parse_against_the_parsed_closed_subset :
  match parsed_closed_subset with
  | Ok ds => map (parse_sequent ds) benchmark_goal_texts
  | Error _ => [] end = map (@Ok sequent) expected_benchmark_sequents.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions validate_definitions_sound.
Print Assumptions validate_sequent_sound.
Print Assumptions parse_definitions_sound.
Print Assumptions parse_sequent_sound.
