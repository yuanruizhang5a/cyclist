From Stdlib Require Import List Bool Arith ZArith String Ascii.
From CyclistRocq.FirstOrderNew Require Export Definitions.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Local Infix "+++" := String.append (at level 60, right associativity).

(** Pure input for the original positive FO grammar. Offsets are zero-based
    character offsets, including whitespace. Parsing always consumes the entire
    input. Raw entry points omit signature/scope validation, but still check
    syntax and definition header/head agreement (the AST has no header field).

    Variables are interned by complete spelling, in first-appearance order,
    starting at zero. A final apostrophe selects [Exist], otherwise [Free].
    The map is shared by both sides of a goal, and by a definition transcript.
    [_] is an ordinary stable identifier. Clause-local scope is supplied by the
    existing freshening operations, not by changing the input spelling.

    Original symbolic bracket tags and nonnegative numeric bracket tags are
    supported. All explicit tags are reserved before parsing; implicit tags
    therefore remain fresh even with respect to explicit tags appearing later.
    Symbolic tag spellings (including apostrophes) are distinct, but tags in the
    current AST have only a [nat] representation, not a variable class.
    No source definition, including the undefined [ADD_2], is repaired. *)
Inductive diagnostic :=
| SyntaxError (offset : nat) (expected : string)
| FuelExhausted (offset : nat)
| UndefinedPredicate (name : string)
| PredicateArityMismatch (name : string) (expected : list nat) (actual : nat)
| FunctionArityMismatch (name : string) (expected actual : nat)
| HeaderHeadMismatch (header head_name : string)
| InconsistentDefinitionArity (name : string) (expected actual : nat)
| AntecedentExistential (v : variable).

Inductive result (A : Type) :=
| Ok (value : A)
| Error (problem : diagnostic).
Arguments Ok {A} _.
Arguments Error {A} _.

Definition bind {A B} (r : result A) (f : A -> result B) : result B :=
  match r with Ok x => f x | Error e => Error e end.
Local Notation "x <- r ;; k" := (bind r (fun x => k))
  (at level 100, r at next level, right associativity).

(** Decimal rendering is bounded by the value, without depending on extraction
    or host-language I/O. Typed diagnostics retain all numerical payloads. *)
Fixpoint decimal_chars (fuel n : nat) : string :=
  match fuel with
  | 0 => ""
  | S f =>
      let digit := String (ascii_of_nat (48 + n mod 10)) EmptyString in
      if Nat.ltb n 10 then digit else decimal_chars f (n / 10) +++ digit
  end.
Definition show_nat n := decimal_chars (S n) n.
Definition show_arities ns :=
  String.concat ", " (map show_nat ns).
Definition diagnostic_message e :=
  match e with
  | SyntaxError pos wanted =>
      "at offset " +++ show_nat pos +++ ": expected " +++ wanted
  | FuelExhausted pos => "parser budget exhausted at offset " +++ show_nat pos
  | UndefinedPredicate p => "undefined predicate: " +++ p
  | PredicateArityMismatch p ns n =>
      "predicate " +++ p +++ ": expected arity " +++ show_arities ns +++
      ", got " +++ show_nat n
  | FunctionArityMismatch p n m =>
      "function " +++ p +++ ": expected arity " +++ show_nat n +++
      ", got " +++ show_nat m
  | HeaderHeadMismatch p q =>
      "definition header " +++ p +++ " does not match clause head " +++ q
  | InconsistentDefinitionArity p n m =>
      "inconsistent definition arity for " +++ p +++ ": " +++ show_nat n +++
      " versus " +++ show_nat m
  | AntecedentExistential v =>
      "primed existential variable in antecedent (id " +++
      show_nat (variable_id v) +++ ")"
  end.

Inductive token_kind :=
| Identifier (name : string) | Integer (value : Z)
| LParen | RParen | LBracket | RBracket | LBrace | RBrace
| Comma | Semicolon | Conjunction | Disjunction | ClauseBar
| Equal | Disequal | Turnstile | Implies.
Record token := { kind : token_kind; position : nat }.
Definition token_kind_eq_dec (x y : token_kind) : {x = y} + {x <> y}.
Proof. decide equality; [apply string_dec | apply Z.eq_dec]. Defined.
Definition token_kind_eqb := eqb_of_dec token_kind_eq_dec.

Definition ascii_between lo hi c :=
  Nat.leb lo (nat_of_ascii c) && Nat.leb (nat_of_ascii c) hi.
Definition digitb c := ascii_between 48 57 c.
Definition letterb c := ascii_between 65 90 c || ascii_between 97 122 c.
Definition identifier_startb c := letterb c || Nat.eqb (nat_of_ascii c) 95.
Definition identifier_charb c :=
  identifier_startb c || digitb c || Nat.eqb (nat_of_ascii c) 39.
Definition whitespaceb c :=
  existsb (Nat.eqb (nat_of_ascii c)) [9; 10; 13; 32].

Fixpoint take_chars (p : ascii -> bool) (s : string) : string * string :=
  match s with
  | EmptyString => ("", "")
  | String c rest =>
      if p c then let '(prefix, suffix) := take_chars p rest in
        (String c prefix, suffix)
      else ("", s)
  end.
Fixpoint integer_value (acc : Z) (s : string) : Z :=
  match s with
  | EmptyString => acc
  | String c rest =>
      integer_value (10 * acc + Z.of_nat (nat_of_ascii c - 48))%Z rest
  end.

Fixpoint lex_fuel (fuel offset : nat) (s : string) : result (list token) :=
  match s with
  | EmptyString => Ok []
  | String c rest =>
    match fuel with
    | 0 => Error (FuelExhausted offset)
    | S f =>
      if whitespaceb c then lex_fuel f (S offset) rest else
      if identifier_startb c then
        let '(word, suffix) := take_chars identifier_charb s in
        ts <- lex_fuel f (offset + String.length word) suffix ;;
        Ok ({| kind := Identifier word; position := offset |} :: ts)
      else if digitb c then
        let '(digits, suffix) := take_chars digitb s in
        ts <- lex_fuel f (offset + String.length digits) suffix ;;
        Ok ({| kind := Integer (integer_value 0 digits); position := offset |} :: ts)
      else
        let emit k size suffix :=
          ts <- lex_fuel f (offset + size) suffix ;;
          Ok ({| kind := k; position := offset |} :: ts) in
        match nat_of_ascii c with
        | 40 => emit LParen 1 rest | 41 => emit RParen 1 rest
        | 91 => emit LBracket 1 rest | 93 => emit RBracket 1 rest
        | 123 => emit LBrace 1 rest | 125 => emit RBrace 1 rest
        | 44 => emit Comma 1 rest | 59 => emit Semicolon 1 rest
        | 38 => emit Conjunction 1 rest
        | 61 => match rest with
                | String d suffix => if Nat.eqb (nat_of_ascii d) 62
                    then emit Implies 2 suffix else emit Equal 1 rest
                | _ => emit Equal 1 rest end
        | 33 => match rest with
                | String d suffix => if Nat.eqb (nat_of_ascii d) 61
                    then emit Disequal 2 suffix
                    else Error (SyntaxError offset "!=")
                | _ => Error (SyntaxError offset "!=") end
        | 124 => match rest with
                 | String d suffix => if Nat.eqb (nat_of_ascii d) 45
                     then emit Turnstile 2 suffix else emit ClauseBar 1 rest
                 | _ => emit ClauseBar 1 rest end
        | 92 => match rest with
                | String d suffix => if Nat.eqb (nat_of_ascii d) 47
                    then emit Disjunction 2 suffix
                    else Error (SyntaxError offset "\\/")
                | _ => Error (SyntaxError offset "\\/") end
        | 43 | 45 =>
            match rest with
            | String d _ => if digitb d then
                let '(digits, suffix) := take_chars digitb rest in
                let value := integer_value 0 digits in
                emit (Integer (if Nat.eqb (nat_of_ascii c) 45 then (- value)%Z
                               else value)) (S (String.length digits)) suffix
              else Error (SyntaxError offset "a digit after the integer sign")
            | _ => Error (SyntaxError offset "a digit after the integer sign")
            end
        | _ => Error (SyntaxError offset "a first-order input token")
        end
    end
  end.
Definition tokenize s := lex_fuel (S (String.length s)) 0 s.

Record input_state := {
  remaining : list token;
  end_offset : nat;
  variable_names : list (string * variable);
  next_variable : nat;
  tag_names : list (string * nat);
  next_tag : nat
}.
Definition input_position st :=
  match st.(remaining) with [] => st.(end_offset) | t :: _ => t.(position) end.
Definition set_remaining ts st :=
  {| remaining := ts; end_offset := st.(end_offset);
     variable_names := st.(variable_names); next_variable := st.(next_variable);
     tag_names := st.(tag_names); next_tag := st.(next_tag) |}.
Fixpoint lookup_name {A} (name : string) (names : list (string * A)) : option A :=
  match names with
  | [] => None
  | (n, v) :: rest => if String.eqb n name then Some v else lookup_name name rest
  end.
Fixpoint primedb s :=
  match s with
  | EmptyString => false
  | String c EmptyString => Nat.eqb (nat_of_ascii c) 39
  | String _ rest => primedb rest
  end.
Definition intern_variable name st : variable * input_state :=
  match lookup_name name st.(variable_names) with
  | Some v => (v, st)
  | None =>
      let v := if primedb name then Exist st.(next_variable)
               else Free st.(next_variable) in
      (v, {| remaining := st.(remaining); end_offset := st.(end_offset);
             variable_names := (name, v) :: st.(variable_names);
             next_variable := S st.(next_variable);
             tag_names := st.(tag_names); next_tag := st.(next_tag) |})
  end.
Definition fresh_tag st : nat * input_state :=
  (st.(next_tag),
   {| remaining := st.(remaining); end_offset := st.(end_offset);
      variable_names := st.(variable_names); next_variable := st.(next_variable);
      tag_names := st.(tag_names); next_tag := S st.(next_tag) |}).

(** Pre-scan every explicit bracket tag, first numeric reservations, then named
    reservations. Looking ahead is necessary for fresh implicit tags. *)
Fixpoint numeric_tag_bound ts :=
  match ts with
  | [] => 0
  | t :: rest =>
      let bound := numeric_tag_bound rest in
      match t.(kind), rest with
      | LBracket, n :: r :: _ =>
          match n.(kind), r.(kind) with
          | Integer z, RBracket =>
              if (0 <=? z)%Z then Nat.max (S (Z.to_nat z)) bound else bound
          | _, _ => bound end
      | _, _ => bound end
  end.
Fixpoint reserve_named_tags ts (names : list (string * nat)) next :=
  match ts with
  | [] => (names, next)
  | t :: rest =>
      let '(names', next') :=
        match t.(kind), rest with
        | LBracket, n :: r :: _ =>
            match n.(kind), r.(kind) with
            | Identifier name, RBracket =>
                match lookup_name name names with
                | Some _ => (names, next)
                | None => ((name, next) :: names, S next)
                end
            | _, _ => (names, next) end
        | _, _ => (names, next) end in
      reserve_named_tags rest names' next'
  end.
Definition initial_state s ts :=
  let '(names, next) := reserve_named_tags ts [] (numeric_tag_bound ts) in
  {| remaining := ts; end_offset := String.length s;
     variable_names := []; next_variable := 0;
     tag_names := names; next_tag := next |}.
Definition expect wanted description st : result input_state :=
  match st.(remaining) with
  | t :: ts => if token_kind_eqb wanted t.(kind) then Ok (set_remaining ts st)
               else Error (SyntaxError (input_position st) description)
  | [] => Error (SyntaxError (input_position st) description)
  end.
Definition at_token wanted st :=
  match st.(remaining) with
  | t :: _ => token_kind_eqb wanted t.(kind)
  | [] => false end.
Definition read_identifier st : result (string * input_state) :=
  match st.(remaining) with
  | t :: ts => match t.(kind) with
               | Identifier name => Ok (name, set_remaining ts st)
               | _ => Error (SyntaxError (input_position st) "an identifier") end
  | [] => Error (SyntaxError (input_position st) "an identifier") end.

(** Structural recursion on fuel covers both nested terms and argument lists.
    Like the original parser, applications must have at least one argument. *)
Fixpoint read_term (fuel : nat) (st : input_state) {struct fuel}
  : result (term * input_state) :=
  match fuel with
  | 0 => Error (FuelExhausted (input_position st))
  | S f =>
    match st.(remaining) with
    | t :: ts =>
      match t.(kind) with
      | Integer z => Ok (Const z, set_remaining ts st)
      | Identifier name =>
          let st' := set_remaining ts st in
          if at_token LParen st' then
            st'' <- expect LParen "(" st' ;;
            parsed <- read_arguments f st'' ;;
            let '(args, rest) := parsed in Ok (Fun name args, rest)
          else let '(v, rest) := intern_variable name st' in Ok (Var v, rest)
      | _ => Error (SyntaxError (input_position st) "a term")
      end
    | [] => Error (SyntaxError (input_position st) "a term") end
  end
with read_arguments (fuel : nat) (st : input_state) {struct fuel}
  : result (list term * input_state) :=
  match fuel with
  | 0 => Error (FuelExhausted (input_position st))
  | S f =>
      parsed <- read_term f st ;;
      let '(t, rest) := parsed in
      if at_token Comma rest then
        more <- expect Comma "," rest ;;
        parsed' <- read_arguments f more ;;
        let '(args, rest') := parsed' in Ok (t :: args, rest')
      else rest' <- expect RParen ", or )" rest ;; Ok ([t], rest')
  end.

Definition read_explicit_tag st : result (nat * input_state) :=
  st' <- expect LBracket "[" st ;;
  match st'.(remaining) with
  | t :: ts =>
      tag <- match t.(kind) with
             | Integer z => if (0 <=? z)%Z then Ok (Z.to_nat z)
                            else Error (SyntaxError t.(position) "a nonnegative tag")
             | Identifier name =>
                 match lookup_name name st'.(tag_names) with
                 | Some tag => Ok tag
                 | None => Error (SyntaxError t.(position) "a reserved bracket tag")
                 end
             | _ => Error (SyntaxError t.(position) "a named or nonnegative numeric tag")
             end ;;
      rest <- expect RBracket "]" (set_remaining ts st') ;; Ok (tag, rest)
  | [] => Error (SyntaxError (input_position st') "a bracket tag")
  end.

Definition read_tagged_predicate fuel st : result (atom * input_state) :=
  named <- read_identifier st ;;
  let '(name, rest) := named in
  tagged <- read_explicit_tag rest ;;
  let '(tag, rest') := tagged in
  args_start <- expect LParen "(" rest' ;;
  parsed <- read_arguments fuel args_start ;;
  let '(args, rest'') := parsed in Ok (Pred tag name args, rest'').
Definition begins_tagged_predicate st :=
  match st.(remaining) with
  | t :: b :: _ =>
      match t.(kind), b.(kind) with Identifier _, LBracket => true | _, _ => false end
  | _ => false end.

Definition read_atom fuel st : result (atom * input_state) :=
  match fuel with
  | 0 => Error (FuelExhausted (input_position st))
  | S f =>
    if begins_tagged_predicate st then read_tagged_predicate f st else
    parsed <- read_term f st ;;
    let '(lhs, rest) := parsed in
    if at_token Equal rest then
      rhs <- expect Equal "=" rest ;;
      parsed' <- read_term f rhs ;;
      let '(rhs_term, rest') := parsed' in Ok (Eq lhs rhs_term, rest')
    else if at_token Disequal rest then
      rhs <- expect Disequal "!=" rest ;;
      parsed' <- read_term f rhs ;;
      let '(rhs_term, rest') := parsed' in Ok (Deq lhs rhs_term, rest')
    else match lhs with
         | Fun name args =>
             let '(tag, rest') := fresh_tag rest in Ok (Pred tag name args, rest')
         | _ => Error (SyntaxError (input_position rest) "=, !=, or predicate arguments")
         end
  end.

Fixpoint read_conjunction fuel st : result (product * input_state) :=
  match fuel with
  | 0 => Error (FuelExhausted (input_position st))
  | S f =>
      parsed <- read_atom f st ;;
      let '(a, rest) := parsed in
      if at_token Conjunction rest then
        more <- expect Conjunction "&" rest ;;
        parsed' <- read_conjunction f more ;;
        let '(p, rest') := parsed' in Ok (a :: p, rest')
      else Ok ([a], rest)
  end.
Definition read_product fuel st : result (product * input_state) :=
  match st.(remaining) with
  | t :: ts =>
      match t.(kind) with
      | Identifier name =>
          if String.eqb name "true" then Ok ([], set_remaining ts st)
          else read_conjunction fuel st
      | _ => read_conjunction fuel st end
  | [] => Error (SyntaxError (input_position st) "true or a nonempty product")
  end.
Fixpoint read_formula fuel st : result (formula * input_state) :=
  match fuel with
  | 0 => Error (FuelExhausted (input_position st))
  | S f =>
      parsed <- read_product f st ;;
      let '(p, rest) := parsed in
      if at_token Disjunction rest then
        more <- expect Disjunction "\\/" rest ;;
        parsed' <- read_formula f more ;;
        let '(ps, rest') := parsed' in Ok (p :: ps, rest')
      else Ok ([p], rest)
  end.
Definition read_sequent fuel st : result (sequent * input_state) :=
  ante_parsed <- read_formula fuel st ;;
  let '(ante, rest) := ante_parsed in
  right_start <- expect Turnstile "|-" rest ;;
  succ_parsed <- read_formula fuel right_start ;;
  let '(succ, rest') := succ_parsed in
  Ok ({| antecedent := ante; succedent := succ |}, rest').

Definition read_clause fuel header st : result (clause * input_state) :=
  parsed <- read_product fuel st ;;
  let '(atoms, rest) := parsed in
  head_start <- expect Implies "=>" rest ;;
  named <- read_identifier head_start ;;
  let '(name, rest') := named in
  if String.eqb header name then
    args_start <- expect LParen "(" rest' ;;
    parsed' <- read_arguments fuel args_start ;;
    let '(args, rest'') := parsed' in
    Ok ({| clause_name := name; head := args; body := atoms |}, rest'')
  else Error (HeaderHeadMismatch header name).
Fixpoint read_clauses fuel header st : result (definitions * input_state) :=
  match fuel with
  | 0 => Error (FuelExhausted (input_position st))
  | S f =>
      parsed <- read_clause f header st ;;
      let '(c, rest) := parsed in
      if at_token ClauseBar rest then
        more <- expect ClauseBar "|" rest ;;
        parsed' <- read_clauses f header more ;;
        let '(cs, rest') := parsed' in Ok (c :: cs, rest')
      else rest' <- expect RBrace "| or }" rest ;; Ok ([c], rest')
  end.
Definition read_definition fuel st : result (definitions * input_state) :=
  named <- read_identifier st ;;
  let '(name, rest) := named in
  cases_start <- expect LBrace "{" rest ;;
  read_clauses fuel name cases_start.
Fixpoint read_definitions fuel st : result (definitions * input_state) :=
  match fuel with
  | 0 => Error (FuelExhausted (input_position st))
  | S f =>
      parsed <- read_definition f st ;;
      let '(cs, rest) := parsed in
      if at_token Semicolon rest then
        more <- expect Semicolon ";" rest ;;
        match more.(remaining) with
        | [] => Ok (cs, more)
        | _ => parsed' <- read_definitions f more ;;
               let '(ds, rest') := parsed' in Ok (cs ++ ds, rest')
        end
      else Ok (cs, rest)
  end.

Definition finish {A} (parsed : result (A * input_state)) : result A :=
  pair <- parsed ;;
  let '(value, rest) := pair in
  match rest.(remaining) with
  | [] => Ok value
  | _ => Error (SyntaxError (input_position rest) "end of input") end.
Definition run_parser_with_fuel {A}
    (parser : nat -> input_state -> result (A * input_state)) fuel s : result A :=
  ts <- lex_fuel fuel 0 s ;;
  finish (parser fuel (initial_state s ts)).
Definition default_budget s := 16 + 4 * String.length s.
Definition run_parser {A} parser s : result A :=
  @run_parser_with_fuel A parser (default_budget s) s.

(** Standalone term/atom/product/formula parsers are syntactic: there is no
    predicate signature supplied. Use validation or [parse_sequent] for checked
    input. No grouping, quantifier, negation, empty application, or false-literal
    extension is silently accepted. [true] denotes the empty product. *)
Definition parse_term : string -> result term := run_parser read_term.
Definition parse_atom : string -> result atom := run_parser read_atom.
Definition parse_product : string -> result product := run_parser read_product.
Definition parse_formula : string -> result formula := run_parser read_formula.
Definition parse_sequent_raw_with_fuel : nat -> string -> result sequent :=
  run_parser_with_fuel read_sequent.
Definition parse_definitions_raw_with_fuel : nat -> string -> result definitions :=
  run_parser_with_fuel read_definitions.
Definition parse_sequent_raw : string -> result sequent := run_parser read_sequent.
Definition parse_definitions_raw : string -> result definitions := run_parser read_definitions.

Definition function_arity_errors name arity :=
  let expected := if String.eqb name "s" then Some 1
                  else if String.eqb name "cons" then Some 2 else None in
  match expected with
  | None => []
  | Some n => if Nat.eqb n arity then [] else [FunctionArityMismatch name n arity]
  end.
Fixpoint term_input_errors t : list diagnostic :=
  match t with
  | Const _ | Var _ => []
  | Fun name args => function_arity_errors name (List.length args) ++
                     flat_map term_input_errors args
  end.
Definition predicate_arities d name :=
  nodup Nat.eq_dec (map (fun c => List.length c.(head)) (clauses_for d name)).
Definition predicate_input_errors d name arity :=
  match predicate_arities d name with
  | [] => [UndefinedPredicate name]
  | ns => if existsb (Nat.eqb arity) ns then []
          else [PredicateArityMismatch name ns arity]
  end.
Definition atom_input_errors d a :=
  match a with
  | Eq l r | Deq l r => term_input_errors l ++ term_input_errors r
  | Pred _ name args => predicate_input_errors d name (List.length args) ++
                         flat_map term_input_errors args
  end.
Definition arity_consistency_errors d c := flat_map
  (fun c' => if String.eqb c.(clause_name) c'.(clause_name) then
     if Nat.eqb (List.length c.(head)) (List.length c'.(head)) then [] else
       [InconsistentDefinitionArity c.(clause_name)
          (List.length c.(head)) (List.length c'.(head))]
   else []) d.
Definition definitions_input_errors d := flat_map
  (fun c => arity_consistency_errors d c ++ flat_map term_input_errors c.(head) ++
            flat_map (atom_input_errors d) c.(body)) d.
Definition antecedent_input_errors j := flat_map
  (fun v => match v with Free _ => [] | Exist _ => [AntecedentExistential v] end)
  (formula_vars j.(antecedent)).
Definition sequent_input_errors d j := antecedent_input_errors j ++
  flat_map (flat_map (atom_input_errors d)) (j.(antecedent) ++ j.(succedent)).

(** Ordered detailed diagnostics are followed by the existing Boolean checks.
    These final checks make the successful-validation contract explicit and
    proved, even if the core's well-formedness criteria are extended later. *)
Definition validate_definitions (d : definitions) : result definitions :=
  match definitions_input_errors d with
  | e :: _ => Error e
  | [] => if definitions_wfb d then Ok d
          else Error (SyntaxError 0 "well-formed definitions")
  end.
Definition validate_sequent (d : definitions) (j : sequent) : result sequent :=
  checked <- validate_definitions d ;;
  match sequent_input_errors checked j with
  | e :: _ => Error e
  | [] => if sequent_wfb checked j then Ok j
          else Error (SyntaxError 0 "a well-formed sequent")
  end.
Definition parse_definitions_with_fuel fuel s : result definitions :=
  d <- parse_definitions_raw_with_fuel fuel s ;; validate_definitions d.
Definition parse_sequent_with_fuel d fuel s : result sequent :=
  j <- parse_sequent_raw_with_fuel fuel s ;; validate_sequent d j.
Definition parse_definitions (s : string) : result definitions :=
  d <- parse_definitions_raw s ;; validate_definitions d.
Definition parse_sequent (d : definitions) (s : string) : result sequent :=
  j <- parse_sequent_raw s ;; validate_sequent d j.

Lemma validate_definitions_sound d checked :
  validate_definitions d = Ok checked -> checked = d /\ definitions_wfb checked = true.
Proof.
  unfold validate_definitions.
  destruct (definitions_input_errors d) as [|e es]; [|discriminate].
  destruct (definitions_wfb d) eqn:H; [|discriminate].
  intro E; inversion E; subst; auto.
Qed.
Lemma validate_sequent_sound d j checked :
  validate_sequent d j = Ok checked ->
  checked = j /\ definitions_wfb d = true /\ sequent_wfb d checked = true.
Proof.
  unfold validate_sequent, bind.
  destruct (validate_definitions d) as [ds|e] eqn:D; [|discriminate].
  apply validate_definitions_sound in D. destruct D as [-> D].
  destruct (sequent_input_errors d j) as [|e es]; [|discriminate].
  destruct (sequent_wfb d j) eqn:H; [|discriminate].
  intro E; inversion E; subst; auto.
Qed.
Theorem parse_definitions_sound s checked :
  parse_definitions s = Ok checked -> definitions_wfb checked = true.
Proof.
  unfold parse_definitions, bind.
  destruct (parse_definitions_raw s) as [d|e]; [|discriminate].
  intro H; apply validate_definitions_sound in H; tauto.
Qed.
Theorem parse_sequent_sound d s checked :
  parse_sequent d s = Ok checked ->
  definitions_wfb d = true /\ sequent_wfb d checked = true.
Proof.
  unfold parse_sequent, bind.
  destruct (parse_sequent_raw s) as [j|e]; [|discriminate].
  intro H; apply validate_sequent_sound in H; tauto.
Qed.
