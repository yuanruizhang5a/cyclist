(** * Verified generation of one local inference

    This is the executable front end to Rules.v, not a proof-search driver.
    [generate_axiom] recognizes structural closing shapes; [generate_rules_in_context]
    scans eligible occurrences; [generate_requested_in_context] checks explicit caller
    choices. Successful results already contain semantic soundness proofs.

    To read the dense constructor cases, compare a rule's literal source and
    ordered target lists with RULE_EXPANSIONS.md and its kernel in Rules.v.
    [verified_build] supplies syntax evidence, then [ensure_rule] checks that
    the result really belongs to the caller's requested judgment. A [None]
    result means no verified candidate was generated, not semantic falsity. *)
From Stdlib Require Import List Bool Arith String Lia Permutation.
From CyclistRocq.LPL Require Import Signature Syntax Semantics Progress Rules.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Module MakeRuleGeneration (L : LANGUAGE) (Syn : SYNTAX L) (Sem : SEMANTICS L Syn)
  (Pr : PROGRESS L Syn Sem) (Kernel : KERNEL L Syn Sem Pr).
(** Reuse the same instantiated kernel as Certification.v. Applying the
    syntax/rule functors again would create distinct inductive types, even
    with the same signature and model; aliases preserve their identity. *)
Export Syn Sem.
Module Export P := Kernel.P.
Module Export K := Kernel.

(** Dependent Boolean branching turns a successful computation into evidence
    available to the constructor. The false branch cannot construct a rule
    requiring that side condition, and therefore returns [None]. *)
Definition guard (b : bool) (build : b = true -> option Cyclic.rule_instance)
    : option Cyclic.rule_instance.
Proof. destruct b eqn:H; [exact (build eq_refl)|exact None]. Defined.

(** Check every premise as well as the source. The resulting [Forall] proof
    is passed to an already proved kernel, never accepted as an axiom. *)
Definition verified_build source targets
    (build : judgment_wfb source = true -> Forall (fun j => judgment_wfb j = true) targets -> Cyclic.rule_instance)
    : option Cyclic.rule_instance.
Proof.
  destruct (judgment_wfb source) eqn:Hs; [|exact None].
  destruct (forallb judgment_wfb targets) eqn:Ht; [|exact None].
  apply Some, (build eq_refl). apply Forall_forall; intros j Hin; apply (proj1 (forallb_forall _ _) Ht j Hin).
Defined.

(** Semantic rule records alone do not enforce the object-language policy.
    This final boundary also checks trace-pair endpoints and that progressing
    pairs belong to the valid pairs, using the unchanged framework's checker. *)
Definition rule_wfb r := judgment_wfb r.(Cyclic.rule_conclusion) &&
  forallb (fun p => judgment_wfb p.(Cyclic.premise_judgment) &&
    Cyclic.edge_info_wfb r.(Cyclic.rule_conclusion) p.(Cyclic.premise_judgment) p.(Cyclic.premise_edge))
    r.(Cyclic.rule_premises).

Definition ensure_rule j candidate :=
  match candidate with
  | None => None
  | Some r => if judgment_eqb r.(Cyclic.rule_conclusion) j && rule_wfb r then Some r else None
  end.

Theorem ensure_rule_spec j candidate r : ensure_rule j candidate = Some r ->
  r.(Cyclic.rule_conclusion) = j /\ judgment_wfb j = true /\
  Forall (fun p => judgment_wfb p.(Cyclic.premise_judgment) = true /\
    Cyclic.edge_info_wfb j p.(Cyclic.premise_judgment) p.(Cyclic.premise_edge) = true) r.(Cyclic.rule_premises).
Proof.
  unfold ensure_rule; destruct candidate as [r'|]; [|discriminate].
  destruct (judgment_eqb r'.(Cyclic.rule_conclusion) j && rule_wfb r') eqn:Hcheck; [|discriminate].
  intro Heq; inversion Heq; subst r'. apply andb_true_iff in Hcheck as [Hconclusion Hwf].
  apply judgment_eqb_spec in Hconclusion. split; [exact Hconclusion|].
  unfold rule_wfb in Hwf; apply andb_true_iff in Hwf as [Hs Hps].
  rewrite Hconclusion in *; split; [exact Hs|]. apply Forall_forall; intros p Hin.
  apply andb_true_iff. exact (proj1 (forallb_forall _ _) Hps p Hin).
Qed.

(** New subformulas receive deterministic fresh tags only when traceable.
    An unfolding may instead continue the principal's existing tag. Distinct
    offsets separate new siblings when both appear in the same premise;
    [rule_wfb] remains the final uniqueness check. *)
Definition tag_for j offset a := if traceableb a then Some (fresh_name (judgment_tags j) + offset) else None.
Definition continue_tag (tag : option nat) a := if traceableb a then tag else None.


(** Generate at one selected right occurrence. [pre]/[post] preserve the
    surrounding context. Inner label matches are intentional: assignment and
    test rules require an exposed final state, whereas temporal rules require
    an exposed initial state. Callers can request explicit label algebra to
    present these shapes; no normalization is attempted here. *)
Section RelationContext.
Context (R : list relation_atom).
Local Notation Jdg := (Rdg R).
Local Notation atom_head_left := (K.atom_head_left R).
Local Notation atom_head_right := (K.atom_head_right R).
Local Notation box_choice_left := (K.box_choice_left R).
Local Notation box_choice_right := (K.box_choice_right R).
Local Notation box_choice_right_base := (K.box_choice_right_base R).
Local Notation box_sequence_left := (K.box_sequence_left R).
Local Notation box_sequence_right := (K.box_sequence_right R).
Local Notation box_sequence_right_base := (K.box_sequence_right_base R).
Local Notation box_star_left := (K.box_star_left R).
Local Notation box_star_right := (K.box_star_right R).
Local Notation box_star_right_base := (K.box_star_right_base R).
Local Notation box_test_left := (K.box_test_left R).
Local Notation box_test_right := (K.box_test_right R).
Local Notation box_test_right_base := (K.box_test_right_base R).
Local Notation conjunction_left := (K.conjunction_left R).
Local Notation conjunction_right := (K.conjunction_right R).
Local Notation cut_rule := (K.cut_rule R).
Local Notation diamond_choice_left := (K.diamond_choice_left R).
Local Notation diamond_choice_right := (K.diamond_choice_right R).
Local Notation diamond_sequence_left := (K.diamond_sequence_left R).
Local Notation diamond_sequence_right := (K.diamond_sequence_right R).
Local Notation diamond_star_left := (K.diamond_star_left R).
Local Notation diamond_star_right := (K.diamond_star_right R).
Local Notation diamond_test_left := (K.diamond_test_left R).
Local Notation diamond_test_right := (K.diamond_test_right R).
Local Notation disjunction_left := (K.disjunction_left R).
Local Notation disjunction_right := (K.disjunction_right R).
Local Notation dual_suffix_left := (K.dual_suffix_left R).
Local Notation dual_suffix_right := (K.dual_suffix_right R).
Local Notation dual_suffix_right_base := (K.dual_suffix_right_base R).
Local Notation enhance_right := (K.enhance_right R).
Local Notation false_right_parts := (K.false_right_parts R).
Local Notation false_right_replacement := (K.false_right_replacement R).
Local Notation first_left := (K.first_left R).
Local Notation first_right := (K.first_right R).
Local Notation implication_left := (K.implication_left R).
Local Notation implication_right := (K.implication_right R).
Local Notation left_conclusion := (K.left_conclusion R).
Local Notation left_equivalent := (K.left_equivalent R).
Local Notation left_label_equivalent := (K.left_label_equivalent R).
Local Notation left_many := (K.left_many R).
Local Notation left_one := (K.left_one R).
Local Notation left_targets := (K.left_targets R).
Local Notation left_two_conjunctive := (K.left_two_conjunctive R).
Local Notation left_two_disjunctive := (K.left_two_disjunctive R).
Local Notation negation_left := (K.negation_left R).
Local Notation negation_right := (K.negation_right R).
Local Notation right_conclusion := (K.right_conclusion R).
Local Notation right_equivalent := (K.right_equivalent R).
Local Notation right_label_equivalent := (K.right_label_equivalent R).
Local Notation right_many := (K.right_many R).
Local Notation right_one := (K.right_one R).
Local Notation right_targets := (K.right_targets R).
Local Notation right_two_disjunctive := (K.right_two_disjunctive R).
Local Notation right_two_equivalent := (K.right_two_equivalent R).
Local Notation suffix_left := (K.suffix_left R).
Local Notation suffix_right := (K.suffix_right R).
Local Notation suffix_right_base := (K.suffix_right_base R).
Local Notation weakening_left := (K.weakening_left R).
Local Notation weakening_right := (K.weakening_right R).
Local Notation wellformed_left_principal := (K.wellformed_left_principal R).
Local Notation wellformed_principal := (K.wellformed_principal R).
(** Finite local action-rule candidates. No action relation is evaluated. *)
Definition atomic_boxright_candidate lhs pre o post y :=
  match o.(occurrence_formula), o.(occurrence_label) with
  | Box (Atomic action payload) body, Join sigma (StateLabel u) =>
    let ta := o.(occurrence_tag) in let tb := continue_tag ta body in
    let source := right_conclusion lhs pre post (Occ (Join sigma (StateLabel u)) (Box (Atomic action payload) body) ta) in
    guard (world_freshb y source) (fun Hfresh =>
      verified_build source
        [Rdg (R ++ [action_relation action payload u (L.world_name y)]) lhs
          (pre ++ Occ (action_label sigma u (L.world_name y)) body tb :: post)]
        (fun Hs Ht => box_atomic_right R lhs pre post sigma u action payload body y ta tb Hs (Forall_inv Ht) Hfresh))
  | _, _ => None end.
Definition atomic_diamondleft_candidate pre o post rhs y :=
  match o.(occurrence_formula), o.(occurrence_label) with
  | Diamond (Atomic action payload) body, Join sigma (StateLabel u) =>
    let ta := o.(occurrence_tag) in
    let source := left_conclusion pre post rhs (Occ (Join sigma (StateLabel u)) (Diamond (Atomic action payload) body) ta) in
    guard (world_freshb y source) (fun Hfresh =>
      verified_build source
        [Rdg (R ++ [action_relation action payload u (L.world_name y)])
          (pre ++ Occ (action_label sigma u (L.world_name y)) body None :: post) rhs]
        (fun Hs Ht => diamond_atomic_left R pre post rhs sigma u action payload body y ta None Hs (Forall_inv Ht) Hfresh))
  | _, _ => None end.
Definition atomic_boxleft_candidate Rpre relation Rpost pre o post rhs :=
  match o.(occurrence_formula), o.(occurrence_label), relation with
  | Box (Atomic action payload) body, Join sigma (StateLabel u), ActionRelation _ _ _ (StateLabel v) =>
    verified_build
      (Rdg (Rpre ++ action_relation action payload u v :: Rpost) (pre ++ Occ (Join sigma (StateLabel u)) (Box (Atomic action payload) body) o.(occurrence_tag) :: post) rhs)
      [Rdg (Rpre ++ Rpost) (pre ++ Occ (action_label sigma u v) body None :: post) rhs]
      (fun Hs Ht => box_atomic_left Rpre Rpost pre post rhs sigma u v action payload body o.(occurrence_tag) None Hs (Forall_inv Ht))
  | _, _, _ => None end.
Definition atomic_diamondright_candidate Rpre relation Rpost lhs pre o post :=
  match o.(occurrence_formula), o.(occurrence_label), relation with
  | Diamond (Atomic action payload) body, Join sigma (StateLabel u), ActionRelation _ _ _ (StateLabel v) =>
    let tb := tag_for (Rdg R lhs (pre ++ o :: post)) 0 body in
    verified_build
      (Rdg (Rpre ++ action_relation action payload u v :: Rpost) lhs (pre ++ Occ (Join sigma (StateLabel u)) (Diamond (Atomic action payload) body) o.(occurrence_tag) :: post))
      [Rdg (Rpre ++ Rpost) lhs (pre ++ Occ (action_label sigma u v) body tb :: post)]
      (fun Hs Ht => diamond_atomic_right Rpre Rpost lhs pre post sigma u v action payload body o.(occurrence_tag) tb Hs (Forall_inv Ht))
  | _, _, _ => None end.
Fixpoint scan_relations pre rest
    (build : list relation_atom -> relation_atom -> list relation_atom -> option Cyclic.rule_instance) :=
  match rest with
  | [] => []
  | relation :: post => build pre relation post :: scan_relations (pre ++ [relation]) post build
  end.

Definition right_at (lhs pre : list occurrence) (o : occurrence) (post : list occurrence) : list (option Cyclic.rule_instance) :=
  let j := right_conclusion lhs pre post o in
  let l := o.(occurrence_label) in
  let ta := o.(occurrence_tag) in
  match o.(occurrence_formula) with
  | Conj a b => let tb := tag_for j 0 a in let tc := tag_for j 1 b in
    [verified_build (right_conclusion lhs pre post (Occ l (Conj a b) ta)) (right_targets lhs pre post [[Occ l a tb];[Occ l b tc]]) (fun Hs Ht => conjunction_right lhs pre post l a b ta tb tc Hs Ht)]
  | Disj a b => let tb := tag_for j 0 a in let tc := tag_for j 1 b in
    [verified_build (right_conclusion lhs pre post (Occ l (Disj a b) ta)) (right_targets lhs pre post [[Occ l a tb;Occ l b tc]]) (fun Hs Ht => disjunction_right lhs pre post l a b ta tb tc Hs Ht)]
  | Neg a => [verified_build (right_conclusion lhs pre post (Occ l (Neg a) ta))
      ([Jdg (lhs ++ [Occ l a None]) (pre ++ post)]) (fun Hs Ht => negation_right lhs pre post l a ta None Hs Ht)]
  | Impl a b => let tc := tag_for j 0 b in [verified_build (right_conclusion lhs pre post (Occ l (Impl a b) ta))
      ([Jdg (lhs ++ [Occ l a None]) (pre ++ Occ l b tc :: post)]) (fun Hs Ht => implication_right lhs pre post l a b ta None tc Hs Ht)]
  | Box p body => match p with
    | Seq a b => let tb := continue_tag ta (Box a (Box b body)) in [verified_build (right_conclusion lhs pre post (Occ l (Box (Seq a b) body) ta)) (right_targets lhs pre post [[Occ l (Box a (Box b body)) tb]]) (fun Hs Ht => box_sequence_right lhs pre post l a b body ta tb Hs Ht)]
    | Choice a b => let tb := continue_tag ta (Box a body) in let tc := continue_tag ta (Box b body) in [verified_build (right_conclusion lhs pre post (Occ l (Box (Choice a b) body) ta)) (right_targets lhs pre post [[Occ l (Box a body) tb];[Occ l (Box b body) tc]]) (fun Hs Ht => box_choice_right lhs pre post l a b body ta tb tc Hs Ht)]
    | Star a => let tb := continue_tag ta (Box (Test Truth) body) in let tc := continue_tag ta (Box a (Box (Star a) body)) in [verified_build (right_conclusion lhs pre post (Occ l (Box (Star a) body) ta)) (right_targets lhs pre post [[Occ l (Box (Test Truth) body) tb];[Occ l (Box a (Box (Star a) body)) tc]]) (fun Hs Ht => box_star_right lhs pre post l a body ta tb tc Hs Ht)]
    | Atomic _ _ => [atomic_boxright_candidate lhs pre o post (fresh_name (judgment_world_names j))]
    | Test guard => match l with
      | Join sigma (StateLabel u) => let tb := continue_tag ta body in
        [verified_build (right_conclusion lhs pre post (Occ (Join sigma (StateLabel u)) (Box (Test guard) body) ta))
        [Jdg (lhs ++ [Occ (Join (StateLabel u) (StateLabel u)) guard None]) (pre ++ Occ (Join (Join sigma (StateLabel u)) (StateLabel u)) body tb :: post)]
        (fun Hs Ht => box_test_right lhs pre post sigma u guard body ta tb Hs Ht)]
      | _ => [] end
    end
  | Diamond p body => match p with
    | Seq a b => let tb := tag_for j 0 (Diamond a (Diamond b body)) in [verified_build (right_conclusion lhs pre post (Occ l (Diamond (Seq a b) body) ta)) (right_targets lhs pre post [[Occ l (Diamond a (Diamond b body)) tb]]) (fun Hs Ht => diamond_sequence_right lhs pre post l a b body ta tb Hs Ht)]
    | Choice a b => let tb := tag_for j 0 (Diamond a body) in let tc := tag_for j 1 (Diamond b body) in [verified_build (right_conclusion lhs pre post (Occ l (Diamond (Choice a b) body) ta)) (right_targets lhs pre post [[Occ l (Diamond a body) tb;Occ l (Diamond b body) tc]]) (fun Hs Ht => diamond_choice_right lhs pre post l a b body ta tb tc Hs Ht)]
    | Star a => let tb := tag_for j 0 (Diamond (Test Truth) body) in let tc := tag_for j 1 (Diamond a (Diamond (Star a) body)) in [verified_build (right_conclusion lhs pre post (Occ l (Diamond (Star a) body) ta)) (right_targets lhs pre post [[Occ l (Diamond (Test Truth) body) tb;Occ l (Diamond a (Diamond (Star a) body)) tc]]) (fun Hs Ht => diamond_star_right lhs pre post l a body ta tb tc Hs Ht)]
    | Atomic _ _ => scan_relations [] R (fun rp rel rq => atomic_diamondright_candidate rp rel rq lhs pre o post)
    | Test guard => match l with
      | Join sigma (StateLabel u) => let tb := tag_for j 0 body in
        let gamma := firstn (Nat.pred (List.length lhs)) lhs in
        [verified_build (right_conclusion (gamma ++ [Occ (Join (StateLabel u) (StateLabel u)) guard None]) pre post
          (Occ (Join sigma (StateLabel u)) (Diamond (Test guard) body) ta))
          [Jdg gamma (pre ++ Occ (Join (Join sigma (StateLabel u)) (StateLabel u)) body tb :: post)]
          (fun Hs Ht => diamond_test_right gamma pre post sigma u guard body ta tb Hs Ht)]
      | _ => [] end
    end
  | First body => match l with
    | Join (StateLabel u) sigma => let tb := tag_for j 0 body in
      [verified_build (right_conclusion lhs pre post (Occ (Join (StateLabel u) sigma) (First body) ta)) (right_targets lhs pre post [[Occ (StateLabel u) body tb]]) (fun Hs Ht => first_right lhs pre post u sigma body ta tb Hs Ht)]
    | _ => [] end
  | Suffix a b => match l with
    | Join (StateLabel u) sigma => let tb := tag_for j 0 b in let tc := tag_for j 1 a in let td := ta in
      [guard (label_nonemptyb sigma) (fun Htail => verified_build (right_conclusion lhs pre post (Occ (Join (StateLabel u) sigma) (Suffix a b) ta)) (right_targets lhs pre post [[Occ sigma b tb; Occ sigma a tc];[Occ sigma b tb; Occ sigma (Suffix a b) td]]) (fun Hs Ht => suffix_right lhs pre post u sigma a b ta tb tc td Htail Hs Ht))]
    | _ => [] end
  | DualSuffix a b => match l with
    | Join (StateLabel u) sigma => let tb := tag_for j 0 b in let tc := tag_for j 1 a in let td := ta in
      [guard (label_nonemptyb sigma) (fun Htail => verified_build (right_conclusion lhs pre post (Occ (Join (StateLabel u) sigma) (DualSuffix a b) ta)) (right_targets lhs pre post [[Occ sigma b tb];[Occ sigma a tc; Occ sigma (DualSuffix a b) td]]) (fun Hs Ht => dual_suffix_right lhs pre post u sigma a b ta tb tc td Htail Hs Ht))]
    | _ => [] end
  | a => match l with
    | Join (StateLabel u) sigma => [guard (atomb a) (fun Ha => verified_build (right_conclusion lhs pre post (Occ (Join (StateLabel u) sigma) a ta)) (right_targets lhs pre post [[Occ (StateLabel u) a None]]) (fun Hs Ht => atom_head_right lhs pre post u sigma a ta None Hs Ht Ha))]
    | _ => [] end
  end.

(** Left generation mirrors the same catalog, including its two-premise
    box-choice/star rules. A few test schemes consume a separately positioned
    guard occurrence; [ensure_rule] checks the reconstructed source exactly,
    preventing a near match from silently changing the caller's context. *)
Definition left_at (pre : list occurrence) (o : occurrence) (post rhs : list occurrence) : list (option Cyclic.rule_instance) :=
  let j := left_conclusion pre post rhs o in
  let l := o.(occurrence_label) in
  let ta := o.(occurrence_tag) in
  match o.(occurrence_formula) with
  | Conj a b => [verified_build (left_conclusion pre post rhs (Occ l (Conj a b) ta)) (left_targets pre post rhs [[Occ l a None;Occ l b None]]) (fun Hs Ht => conjunction_left pre post rhs l a b ta None None Hs Ht)]
  | Disj a b => [verified_build (left_conclusion pre post rhs (Occ l (Disj a b) ta)) (left_targets pre post rhs [[Occ l a None];[Occ l b None]]) (fun Hs Ht => disjunction_left pre post rhs l a b ta None None Hs Ht)]
  | Neg a => let tb := tag_for j 0 a in
    [verified_build (left_conclusion pre post rhs (Occ l (Neg a) ta)) ([Jdg (pre ++ post) (Occ l a tb :: rhs)]) (fun Hs Ht => negation_left pre post rhs l a ta tb Hs Ht)]
  | Impl a b => let tb := tag_for j 0 a in
    [verified_build (left_conclusion pre post rhs (Occ l (Impl a b) ta)) ([Jdg (pre ++ post) (Occ l a tb :: rhs);Jdg (pre ++ Occ l b None :: post) rhs]) (fun Hs Ht => implication_left pre post rhs l a b ta tb None Hs Ht)]
  | Box p body => match p with
    | Seq a b => [verified_build (left_conclusion pre post rhs (Occ l (Box (Seq a b) body) ta)) (left_targets pre post rhs [[Occ l (Box a (Box b body)) None]]) (fun Hs Ht => box_sequence_left pre post rhs l a b body ta None Hs Ht)]
    | Choice a b => [verified_build (left_conclusion pre post rhs (Occ l (Box (Choice a b) body) ta)) (left_targets pre post rhs [[Occ l (Box a body) None];[Occ l (Box b body) None]]) (fun Hs Ht => box_choice_left pre post rhs l a b body ta None None Hs Ht)]
    | Star a => [verified_build (left_conclusion pre post rhs (Occ l (Box (Star a) body) ta)) (left_targets pre post rhs [[Occ l (Box (Test Truth) body) None];[Occ l (Box a (Box (Star a) body)) None]]) (fun Hs Ht => box_star_left pre post rhs l a body ta None None Hs Ht)]
    | Atomic _ _ => scan_relations [] R (fun rp rel rq => atomic_boxleft_candidate rp rel rq pre o post rhs)
    | Test guard => match l, post with
      | Join sigma (StateLabel u), _ :: rest =>
        [verified_build (Jdg (pre ++ Occ (Join sigma (StateLabel u)) (Box (Test guard) body) ta :: Occ (Join (StateLabel u) (StateLabel u)) guard None :: rest) rhs)
          [Jdg (pre ++ Occ (Join (Join sigma (StateLabel u)) (StateLabel u)) body None :: rest) rhs]
          (fun Hs Ht => box_test_left pre rest rhs sigma u guard body ta None Hs Ht)]
      | _, _ => [] end
    end
  | Diamond p body => match p with
    | Seq a b => [verified_build (left_conclusion pre post rhs (Occ l (Diamond (Seq a b) body) ta)) (left_targets pre post rhs [[Occ l (Diamond a (Diamond b body)) None]]) (fun Hs Ht => diamond_sequence_left pre post rhs l a b body ta None Hs Ht)]
    | Choice a b => [verified_build (left_conclusion pre post rhs (Occ l (Diamond (Choice a b) body) ta)) (left_targets pre post rhs [[Occ l (Diamond a body) None];[Occ l (Diamond b body) None]]) (fun Hs Ht => diamond_choice_left pre post rhs l a b body ta None None Hs Ht)]
    | Star a => [verified_build (left_conclusion pre post rhs (Occ l (Diamond (Star a) body) ta)) (left_targets pre post rhs [[Occ l (Diamond (Test Truth) body) None];[Occ l (Diamond a (Diamond (Star a) body)) None]]) (fun Hs Ht => diamond_star_left pre post rhs l a body ta None None Hs Ht)]
    | Atomic _ _ => [atomic_diamondleft_candidate pre o post rhs (fresh_name (judgment_world_names j))]
    | Test guard => match l with
      | Join sigma (StateLabel u) =>
        [verified_build (left_conclusion pre post rhs (Occ (Join sigma (StateLabel u)) (Diamond (Test guard) body) ta))
          [Jdg (pre ++ Occ (Join (Join sigma (StateLabel u)) (StateLabel u)) body None :: Occ (Join (StateLabel u) (StateLabel u)) guard None :: post) rhs]
          (fun Hs Ht => diamond_test_left pre post rhs sigma u guard body ta None Hs Ht)]
      | _ => [] end
    end
  | First body => match l with
    | Join (StateLabel u) sigma => [verified_build (left_conclusion pre post rhs (Occ (Join (StateLabel u) sigma) (First body) ta)) (left_targets pre post rhs [[Occ (StateLabel u) body None]]) (fun Hs Ht => first_left pre post rhs u sigma body ta None Hs Ht)]
    | _ => [] end
  | Suffix a b => match l with
    | Join (StateLabel u) sigma => [guard (label_nonemptyb sigma) (fun Htail => verified_build (left_conclusion pre post rhs (Occ (Join (StateLabel u) sigma) (Suffix a b) ta)) (left_targets pre post rhs [[Occ sigma b None];[Occ sigma a None;Occ sigma (Suffix a b) None]]) (fun Hs Ht => suffix_left pre post rhs u sigma a b ta None None None Htail Hs Ht))]
    | _ => [] end
  | DualSuffix a b => match l with
    | Join (StateLabel u) sigma => [guard (label_nonemptyb sigma) (fun Htail => verified_build (left_conclusion pre post rhs (Occ (Join (StateLabel u) sigma) (DualSuffix a b) ta)) (left_targets pre post rhs [[Occ sigma b None;Occ sigma a None];[Occ sigma b None;Occ sigma (DualSuffix a b) None]]) (fun Hs Ht => dual_suffix_left pre post rhs u sigma a b ta None None None Htail Hs Ht))]
    | _ => [] end
  | a => match l with
    | Join (StateLabel u) sigma => [guard (atomb a) (fun Ha => verified_build (left_conclusion pre post rhs (Occ (Join (StateLabel u) sigma) a ta)) (left_targets pre post rhs [[Occ (StateLabel u) a None]]) (fun Hs Ht => atom_head_left pre post rhs u sigma a ta None Hs Ht Ha))]
    | _ => [] end
  end.

(** Move one occurrence at a time from [rest] into [pre]. This finite scan
    preserves order and covers non-head positions. It enumerates local
    alternatives only; it never recurses into newly generated proof goals. *)
(** FOPL reuses all common cases and supplies its assignment/binder cases. *)
Definition right_regular_at lhs pre o post :=
  match o.(occurrence_formula) with
  | Box (Atomic _ _) _ | Diamond (Atomic _ _) _ => []
  | _ => right_at lhs pre o post end.
Definition left_regular_at pre o post rhs :=
  match o.(occurrence_formula) with
  | Box (Atomic _ _) _ | Diamond (Atomic _ _) _ => []
  | _ => left_at pre o post rhs end.

Fixpoint scan_occurrences pre rest
    (build : list occurrence -> occurrence -> list occurrence -> list (option Cyclic.rule_instance)) :=
  match rest with
  | [] => []
  | o :: post => build pre o post ++ scan_occurrences (pre ++ [o]) post build end.
Definition scan_right lhs pre rest := scan_occurrences pre rest (fun p o q => right_at lhs p o q).
Definition scan_left pre rest rhs := scan_occurrences pre rest (fun p o q => left_at p o q rhs).
Fixpoint accepted_rules j candidates :=
  match candidates with
  | [] => []
  | candidate :: rest => match ensure_rule j candidate with
    | Some r => r :: accepted_rules j rest | None => accepted_rules j rest end
  end.
(** Stop at the manual pure boundary. Generic Boolean/quantifier kernels are
    still available by explicit request, but this scan does not become a
    tactic for solving arbitrary pure-FOL sequents. *)
Definition generate_rules_in_context j :=
  accepted_rules j (scan_left [] j.(antecedent) j.(succedent) ++ scan_right j.(antecedent) [] j.(succedent)).

Theorem accepted_rules_spec j candidates r : In r (accepted_rules j candidates) ->
  r.(Cyclic.rule_conclusion) = j /\ judgment_wfb j = true /\
  Forall (fun p => judgment_wfb p.(Cyclic.premise_judgment) = true /\
    Cyclic.edge_info_wfb j p.(Cyclic.premise_judgment) p.(Cyclic.premise_edge) = true) r.(Cyclic.rule_premises).
Proof.
  induction candidates as [|candidate rest IH]; cbn; [contradiction|].
  destruct (ensure_rule j candidate) as [r'|] eqn:H; [intros [->|Hin]|intro Hin];
    [eapply ensure_rule_spec; exact H|apply IH; exact Hin|apply IH; exact Hin].
Qed.
(** These guarantees describe successful candidates, not completeness of the
    scan. Semantic soundness is already stored in each returned rule record. *)
Theorem generate_rules_spec j r : In r (generate_rules_in_context j) -> r.(Cyclic.rule_conclusion) = j /\ judgment_wfb j = true /\
  Forall (fun p => judgment_wfb p.(Cyclic.premise_judgment) = true /\
    Cyclic.edge_info_wfb j p.(Cyclic.premise_judgment) p.(Cyclic.premise_edge) = true) r.(Cyclic.rule_premises).
Proof. unfold generate_rules_in_context; apply accepted_rules_spec. Qed.

Definition ensure_axiom j candidate :=
  match candidate with None => None | Some a =>
    if judgment_eqb a.(Cyclic.axiom_conclusion) j then Some a else None end.

(** The axiom scans carry inclusion proofs while traversing a sublist, so a
    discovered matching occurrence comes with its membership in the original
    judgment. Only identity, false-left, truth-right and singleton suffix-left
    are recognized; arbitrary atomic truth needs a caller's shallow proof. *)
Fixpoint identity_scan j (Hwf : judgment_wfb j = true) o (Hl : In o j.(antecedent)) context
    (Hsub : forall r, In r context -> In r j.(succedent)) : option Cyclic.axiom_instance.
Proof.
  destruct context as [|r rest]; [exact None|].
  destruct (label_eq_dec o.(occurrence_label) r.(occurrence_label)) as [Hlabel|Hlabel].
  - destruct (formula_eq_dec o.(occurrence_formula) r.(occurrence_formula)) as [Hformula|Hformula].
    + exact (Some (identity_axiom j Hwf o r Hl (Hsub r (or_introl eq_refl)) Hlabel Hformula)).
    + exact (identity_scan j Hwf o Hl rest (fun r Hin => Hsub r (or_intror Hin))).
  - exact (identity_scan j Hwf o Hl rest (fun r Hin => Hsub r (or_intror Hin))).
Defined.

Definition first_axiom (a b : option Cyclic.axiom_instance) := match a with Some a => Some a | None => b end.

Fixpoint left_axiom_scan j (Hwf : judgment_wfb j = true) context (Hsub : forall o, In o context -> In o j.(antecedent))
    : option Cyclic.axiom_instance.
Proof.
  destruct context as [|o rest]; [exact None|].
  refine (first_axiom (identity_scan j Hwf o (Hsub o (or_introl eq_refl)) j.(succedent) (fun r Hin => Hin)) _).
  destruct (formula_eq_dec o.(occurrence_formula) Falsity) as [Hfalse|Hfalse].
  - exact (Some (falsity_left_axiom j Hwf o (Hsub o (or_introl eq_refl)) Hfalse)).
  - destruct (occurrence_formula o) eqn:Hformula.
    all: try (lazymatch type of Hformula with
      | _ = Suffix ?a ?b => destruct (occurrence_label o) eqn:Hlabel;
          try exact (Some (suffix_singleton_axiom j Hwf o u a b (Hsub o (or_introl eq_refl)) Hlabel Hformula))
      end).
    all: exact (left_axiom_scan j Hwf rest (fun o Hin => Hsub o (or_intror Hin))).
Defined.

Fixpoint right_axiom_scan j (Hwf : judgment_wfb j = true) context (Hsub : forall o, In o context -> In o j.(succedent))
    : option Cyclic.axiom_instance.
Proof.
  destruct context as [|o rest]; [exact None|].
  destruct (formula_eq_dec o.(occurrence_formula) Truth) as [Htruth|Htruth].
  - exact (Some (truth_right_axiom j Hwf o (Hsub o (or_introl eq_refl)) Htruth)).
  - exact (right_axiom_scan j Hwf rest (fun o Hin => Hsub o (or_intror Hin))).
Defined.

(** The decision returns the equality proof [Hwf] needed by every axiom
    constructor. Weakening is deliberately absent: it always leaves one
    premise, even when that premise is the empty-context sequent. *)
Definition generate_axiom (j : judgment) : option Cyclic.axiom_instance :=
  match Bool.bool_dec (judgment_wfb j) true with
  | left Hwf => ensure_axiom j (first_axiom (left_axiom_scan j Hwf j.(antecedent) (fun o Hin => Hin))
    (right_axiom_scan j Hwf j.(succedent) (fun o Hin => Hin)))
  | right _ => None end.

Lemma ensure_axiom_spec j candidate a : ensure_axiom j candidate = Some a -> a.(Cyclic.axiom_conclusion) = j.
Proof.
  unfold ensure_axiom; destruct candidate as [a'|]; [|discriminate].
  destruct (judgment_eqb a'.(Cyclic.axiom_conclusion) j) eqn:Heq; [|discriminate].
  intro H; inversion H; subst; now apply judgment_eqb_spec in Heq.
Qed.
Theorem generate_axiom_spec j a : generate_axiom j = Some a ->
  a.(Cyclic.axiom_conclusion) = j /\ judgment_wfb j = true.
Proof.
  unfold generate_axiom; destruct (Bool.bool_dec (judgment_wfb j) true) as [Hwf|Hwf]; [|discriminate].
  intro H; split; [eapply ensure_axiom_spec; exact H|exact Hwf].
Qed.

Inductive side := OnLeft | OnRight.
(** Requests make all non-enumerable choices explicit: instantiating terms,
    eigenvariables, substitutions, cut partitions and backlink companions.
    Positions are zero-based. The label-algebra requests also take an explicit
    tree path; supplying an original judgment fixes the intended premise. *)
Inductive rule_request :=
| Local (location : side) (position : nat) (name : string)
| Weaken (location : side) (position : nat)
| SubstituteWorld (original : judgment) (variable : nat) (u : L.world_term)
| SubstituteTrace (original : judgment) (variable : nat) (l : label)
| Cut (gamma sigma delta lambda : list occurrence) (cutformula : occurrence)
| ExchangeAdjacent (location : side) (position : nat)
| BacklinkExact (companion : judgment)
| BacklinkTags (renaming : list (nat * nat)) (companion : judgment)
| RotateLabels (original : judgment) (path : list bool) (rotate_left : bool)
| UnitLabels (original : judgment) (path : list bool) (on_left insert : bool)
| AtomicEigen (location : side) (position successor : nat)
| AtomicUse (location : side) (position relation_index : nat)
| WeakenRelation (position : nat)
| ContractRelation (position : nat)
| ExchangeRelation (position : nat)
| CutRelations (Rgamma Rsigma : list relation_atom)
    (gamma sigma delta lambda : list occurrence) (cutformula : occurrence).

(** Finite tag mappings use the first matching pair and otherwise leave a
    tag unchanged. The generated target's well-formedness rejects collisions;
    [generate_requested_in_context] also checks the entire supplied companion judgment. *)
Fixpoint rename_lookup renaming x :=
  match renaming with [] => x | (a,b)::rest => if Nat.eqb x a then b else rename_lookup rest x end.

Definition at_position (context : list occurrence) n :=
  match nth_error context n with
  | None => None
  | Some o => Some (firstn n context, o, skipn (Datatypes.S n) context)
  end.

Fixpoint named_candidate name candidates :=
  match candidates with
  | [] => None
  | None :: rest => named_candidate name rest
  | Some r :: rest => if String.eqb name r.(Cyclic.rule_name) then Some r else named_candidate name rest
  end.

(** Recover the exact context split at the requested position, then dispatch
    only the requested scheme. Even an unused term is checked for arity: a
    vacuous quantifier body must not accept a malformed request parameter. *)
Definition requested_at j location n request :=
  let context := match location with OnLeft => j.(antecedent) | OnRight => j.(succedent) end in
  match at_position context n with
  | None => None
  | Some (pre,o,post) =>
    let l := o.(occurrence_label) in
    let ta := o.(occurrence_tag) in
    match request, location, o.(occurrence_formula) with
    | Local _ _ name, OnLeft, _ => named_candidate name (left_at pre o post j.(succedent))
    | Local _ _ name, OnRight, _ => named_candidate name (right_at j.(antecedent) pre o post)
    | Weaken _ _, OnLeft, _ => verified_build (left_conclusion pre post j.(succedent) o)
        (left_targets pre post j.(succedent) [[]]) (fun Hs Ht => weakening_left pre post j.(succedent) o Hs Ht)
    | Weaken _ _, OnRight, _ => verified_build (right_conclusion j.(antecedent) pre post o)
        (right_targets j.(antecedent) pre post [[]]) (fun Hs Ht => weakening_right j.(antecedent) pre post o Hs Ht)
    | ExchangeAdjacent _ _, OnLeft, _ => match post with
      | next :: tail => verified_build (Jdg (pre ++ o :: next :: tail) j.(succedent))
          [Jdg (pre ++ next :: o :: tail) j.(succedent)]
          (fun Hs Ht => exchange_rule _ _ Hs Ht eq_refl
            (Permutation_app_head pre (perm_swap next o tail)) (Permutation_refl _))
      | [] => None end
    | ExchangeAdjacent _ _, OnRight, _ => match post with
      | next :: tail => verified_build (Jdg j.(antecedent) (pre ++ o :: next :: tail))
          [Jdg j.(antecedent) (pre ++ next :: o :: tail)]
          (fun Hs Ht => exchange_rule _ _ Hs Ht eq_refl
            (Permutation_refl _) (Permutation_app_head pre (perm_swap next o tail)))
      | [] => None end
    | _, _, _ => None
    end
  end.

(** Non-positional requests construct their literal source and premise
    judgments here. For substitution the original is the premise and its
    substituted image is the conclusion. The public wrapper below checks
    that this constructed conclusion equals [j]. *)
Definition atomic_eigen_requested j location n y :=
  let context := match location with OnLeft => j.(antecedent) | OnRight => j.(succedent) end in
  match at_position context n with
  | None => None
  | Some (pre,o,post) => match location with
    | OnRight => atomic_boxright_candidate j.(antecedent) pre o post y
    | OnLeft => atomic_diamondleft_candidate pre o post j.(succedent) y end
  end.
Definition atomic_use_requested j location n relation_index :=
  let context := match location with OnLeft => j.(antecedent) | OnRight => j.(succedent) end in
  match at_position context n, nth_error R relation_index with
  | Some (pre,o,post), Some relation =>
    let rp := firstn relation_index R in let rq := skipn (S relation_index) R in
    match location with
    | OnLeft => atomic_boxleft_candidate rp relation rq pre o post j.(succedent)
    | OnRight => atomic_diamondright_candidate rp relation rq j.(antecedent) pre o post end
  | _, _ => None end.
Definition relation_requested j n (contract : bool) :=
  match nth_error R n with
  | None => None
  | Some relation => let rp := firstn n R in let rq := skipn (S n) R in
    let source := Rdg (rp ++ relation :: rq) j.(antecedent) j.(succedent) in
    if contract then
      verified_build source [Rdg (rp ++ relation :: relation :: rq) j.(antecedent) j.(succedent)]
        (fun Hs Ht => relation_contraction rp rq relation j.(antecedent) j.(succedent) Hs Ht)
    else
      verified_build source [Rdg (rp ++ rq) j.(antecedent) j.(succedent)]
        (fun Hs Ht => relation_weakening rp rq relation j.(antecedent) j.(succedent) Hs Ht)
  end.
Definition relation_exchange_requested j n :=
  match skipn n R with
  | a :: b :: rest => let rp := firstn n R in
      verified_build (Rdg (rp ++ a :: b :: rest) j.(antecedent) j.(succedent))
        [Rdg (rp ++ b :: a :: rest) j.(antecedent) j.(succedent)]
        (fun Hs Ht => relation_exchange _ _ Hs Ht eq_refl eq_refl
          (Permutation_app_head rp (perm_swap b a rest)))
  | _ => None end.

Definition raw_requested j request :=
  match request with
  | CutRelations Rgamma Rsigma gamma sigma delta lambda cutformula =>
      verified_build (Rdg (Rgamma ++ Rsigma) (gamma ++ sigma) (delta ++ lambda))
        [Rdg Rgamma gamma (cutformula :: delta);Rdg Rsigma (sigma ++ [cutformula]) lambda]
        (fun Hs Ht => cut_relations Rgamma Rsigma gamma sigma delta lambda cutformula Hs Ht)
  | AtomicEigen location n y => atomic_eigen_requested j location n y
  | AtomicUse location n index => atomic_use_requested j location n index
  | WeakenRelation n => relation_requested j n false
  | ContractRelation n => relation_requested j n true
  | ExchangeRelation n => relation_exchange_requested j n
  | Local location n _ | Weaken location n | ExchangeAdjacent location n =>
      requested_at j location n request
  | SubstituteWorld original x u => guard (L.world_term_wfb u) (fun _ =>
      verified_build (map_labels (subst_world_label x u) original) [original]
        (fun Hs Ht => world_substitution_rule original x u (Forall_inv Ht) Hs))
  | SubstituteTrace original x l => guard (label_wfb l) (fun _ => guard (label_nonemptyb l) (fun Hne =>
      verified_build (map_labels (subst_trace_label x l) original) [original]
        (fun Hs Ht => trace_substitution_rule original x l Hne (Forall_inv Ht) Hs)))
  | UnitLabels original path on_left insert =>
      verified_build (map_labels (unit_label path on_left insert) original) [original]
        (fun Hs Ht => label_unit_rule original path on_left insert (Forall_inv Ht) Hs)
  | RotateLabels original path rotate_left =>
      verified_build (map_labels (rotate_label path rotate_left) original) [original]
        (fun Hs Ht => label_rotation_rule original path rotate_left (Forall_inv Ht) Hs)
  | Cut gamma sigma delta lambda cutformula =>
      verified_build (Jdg (gamma ++ sigma) (delta ++ lambda))
        [Jdg gamma (cutformula :: delta);Jdg (sigma ++ [cutformula]) lambda]
        (fun Hs Ht => cut_rule gamma sigma delta lambda cutformula Hs Ht)
  | BacklinkExact companion => verified_build companion [companion]
      (fun Hs Ht => exact_backlink companion Hs)
  | BacklinkTags renaming companion =>
      verified_build j [rename_tags (rename_lookup renaming) j]
        (fun Hs Ht => tag_renaming_backlink j (rename_lookup renaming) Hs (Forall_inv Ht))
  end.

(** Tag-renaming needs an extra companion comparison because its kernel can
    construct a renamed judgment directly from [j]. Exact backlinks instead
    reconstruct the source from their companion and are checked by the same
    [ensure_rule] conclusion equality as every other request. *)
Definition generate_requested_in_context j request :=
  match request with
  | BacklinkTags renaming companion =>
      if judgment_eqb (rename_tags (rename_lookup renaming) j) companion
      then ensure_rule j (raw_requested j request) else None
  | _ => ensure_rule j (raw_requested j request)
  end.

Theorem generate_requested_spec j request r : generate_requested_in_context j request = Some r ->
  r.(Cyclic.rule_conclusion) = j /\ judgment_wfb j = true /\
  Forall (fun p => judgment_wfb p.(Cyclic.premise_judgment) = true /\
    Cyclic.edge_info_wfb j p.(Cyclic.premise_judgment) p.(Cyclic.premise_edge) = true) r.(Cyclic.rule_premises).
Proof.
  unfold generate_requested_in_context; destruct request; try apply ensure_rule_spec.
  destruct (judgment_eqb _ _); [apply ensure_rule_spec|discriminate].
Qed.
End RelationContext.
Definition generate_rules j := generate_rules_in_context (relations j) j.
Definition generate_requested j req := generate_requested_in_context (relations j) j req.
Theorem all_generated_rules_spec j r : In r (generate_rules j) ->
  r.(Cyclic.rule_conclusion) = j /\ judgment_wfb j = true /\
  Forall (fun p => judgment_wfb p.(Cyclic.premise_judgment) = true /\
    Cyclic.edge_info_wfb j p.(Cyclic.premise_judgment) p.(Cyclic.premise_edge) = true) r.(Cyclic.rule_premises).
Proof. apply generate_rules_spec. Qed.
Theorem requested_rule_spec j req r : generate_requested j req = Some r ->
  r.(Cyclic.rule_conclusion) = j /\ judgment_wfb j = true /\
  Forall (fun p => judgment_wfb p.(Cyclic.premise_judgment) = true /\
    Cyclic.edge_info_wfb j p.(Cyclic.premise_judgment) p.(Cyclic.premise_edge) = true) r.(Cyclic.rule_premises).
Proof. apply generate_requested_spec. Qed.
End MakeRuleGeneration.
