(** * Verified generation of one local inference

    This is the executable front end to Rules.v, not a proof-search driver.
    [generate_axiom] recognizes structural closing shapes; [generate_rules]
    scans eligible occurrences; [generate_requested] checks explicit caller
    choices. Successful results already contain semantic soundness proofs.

    To read the dense constructor cases, compare a rule's literal source and
    ordered target lists with RULE_EXPANSIONS.md and its kernel in Rules.v.
    [verified_build] supplies syntax evidence, then [ensure_rule] checks that
    the result really belongs to the caller's requested judgment. A [None]
    result means no verified candidate was generated, not semantic falsity. *)
From Stdlib Require Import List Bool Arith String Lia Permutation.
From CyclistRocq.LPL.FOPL Require Import Signature Rules.
From CyclistRocq.LPL Require Import RuleGeneration.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Module MakeRuleGeneration (S : SIGNATURE) (Kernel : KERNEL S).
Module Export Common := CyclistRocq.LPL.RuleGeneration.MakeRuleGeneration
  Kernel.Core.Pr.Sem.Syn.Language Kernel.Core.Pr.Sem.Syn.Shared
  Kernel.Core.Pr.Sem.Shared Kernel.Core.Pr.Shared Kernel.SharedKernel.
Module Export Sem := Kernel.Core.Pr.Sem.
Module Export Syn := Sem.Syn.
Module Export P := Kernel.P.
(* Export the supplied kernel directly. Copying its factory into another
   module alias loses generative sharing in Rocq 9.1's separate checker. *)
Export Kernel.
Definition fresh_eigen j l a := fresh_name (judgment_vars j ++ label_vars l ++ formula_vars a).
Definition right_special (lhs pre : list occurrence) (o : occurrence) (post : list occurrence) : list (option Cyclic.rule_instance) :=
  let j := right_conclusion lhs pre post o in
  let l := o.(occurrence_label) in
  let ta := o.(occurrence_tag) in
  match o.(occurrence_formula) with
  | All u body => let v := fresh_eigen (Jdg lhs (pre ++ post)) l body in
    [guard (pureb body) (fun Hp => guard (eigen_freshb v (Jdg lhs (pre ++ post)) l body) (fun Hfresh =>
      verified_build (right_conclusion lhs pre post (Occ l (All u body) None))
        [right_conclusion lhs pre post (Occ l (subst_fo u (Var v) body) None)]
        (fun Hs Ht => universal_right lhs pre post l u v body Hp Hfresh Hs (Forall_inv Ht))))]
  | Box p body => match p with
    | Assign x t => match l with
      | Join sigma (StateLabel u) => let tb := continue_tag ta body in
        [verified_build (right_conclusion lhs pre post (Occ (Join sigma (StateLabel u)) (Box (Assign x t) body) ta)) (right_targets lhs pre post [[Occ (Join (Join sigma (StateLabel u)) (StateLabel (AssignUpdate x t u))) body tb]]) (fun Hs Ht => box_assignment_right lhs pre post sigma u x t body ta tb Hs Ht)]
      | _ => [] end
    | _ => [] end
  | Diamond p body => match p with
    | Assign x t => match l with
      | Join sigma (StateLabel u) => let tb := continue_tag ta body in
        [verified_build (right_conclusion lhs pre post (Occ (Join sigma (StateLabel u)) (Diamond (Assign x t) body) ta)) (right_targets lhs pre post [[Occ (Join (Join sigma (StateLabel u)) (StateLabel (AssignUpdate x t u))) body tb]]) (fun Hs Ht => diamond_assignment_right lhs pre post sigma u x t body ta tb Hs Ht)]
      | _ => [] end
    | _ => [] end
  | _ => [] end.
Definition right_at lhs pre o post :=
  Common.right_regular_at [] lhs pre o post ++ right_special lhs pre o post.
Definition left_special (pre : list occurrence) (o : occurrence) (post rhs : list occurrence) : list (option Cyclic.rule_instance) :=
  let j := left_conclusion pre post rhs o in
  let l := o.(occurrence_label) in
  let ta := o.(occurrence_tag) in
  match o.(occurrence_formula) with
  | Ex u body => let v := fresh_eigen (Jdg (pre ++ post) rhs) l body in
    [guard (pureb body) (fun Hp => guard (eigen_freshb v (Jdg (pre ++ post) rhs) l body) (fun Hfresh =>
      verified_build (left_conclusion pre post rhs (Occ l (Ex u body) None))
        [left_conclusion pre post rhs (Occ l (subst_fo u (Var v) body) None)]
        (fun Hs Ht => existential_left pre post rhs l u v body Hp Hfresh Hs (Forall_inv Ht))))]
  | Box p body => match p with
    | Assign x t => match l with
      | Join sigma (StateLabel u) =>
        [verified_build (left_conclusion pre post rhs (Occ (Join sigma (StateLabel u)) (Box (Assign x t) body) ta)) (left_targets pre post rhs [[Occ (Join (Join sigma (StateLabel u)) (StateLabel (AssignUpdate x t u))) body None]]) (fun Hs Ht => box_assignment_left pre post rhs sigma u x t body ta None Hs Ht)]
      | _ => [] end
    | _ => [] end
  | Diamond p body => match p with
    | Assign x t => match l with
      | Join sigma (StateLabel u) =>
        [verified_build (left_conclusion pre post rhs (Occ (Join sigma (StateLabel u)) (Diamond (Assign x t) body) ta)) (left_targets pre post rhs [[Occ (Join (Join sigma (StateLabel u)) (StateLabel (AssignUpdate x t u))) body None]]) (fun Hs Ht => diamond_assignment_left pre post rhs sigma u x t body ta None Hs Ht)]
      | _ => [] end
    | _ => [] end
  | _ => [] end.
Definition left_at pre o post rhs :=
  Common.left_regular_at [] pre o post rhs ++ left_special pre o post rhs.
Definition scan_right lhs pre rest := Common.scan_occurrences pre rest (fun p o q => right_at lhs p o q).
Definition scan_left pre rest rhs := Common.scan_occurrences pre rest (fun p o q => left_at p o q rhs).
Definition generate_rules j :=
  if pure_terminalb j then [] else
  accepted_rules j (scan_left [] j.(antecedent) j.(succedent) ++ scan_right j.(antecedent) [] j.(succedent)).

Theorem generate_rules_spec j r : In r (generate_rules j) -> r.(Cyclic.rule_conclusion) = j /\ judgment_wfb j = true /\
  Forall (fun p => judgment_wfb p.(Cyclic.premise_judgment) = true /\
    Cyclic.edge_info_wfb j p.(Cyclic.premise_judgment) p.(Cyclic.premise_edge) = true) r.(Cyclic.rule_premises).
Proof. unfold generate_rules; destruct (pure_terminalb j); [cbn; tauto|apply accepted_rules_spec]. Qed.

Inductive rule_request :=
| Local (location : side) (position : nat) (name : string)
| Weaken (location : side) (position : nat)
| Instantiate (location : side) (position : nat) (t : term)
| Eigen (location : side) (position variable : nat)
| SubstituteWorld (original : judgment) (variable : nat) (u : update)
| SubstituteTrace (original : judgment) (variable : nat) (l : label)
| Cut (gamma sigma delta lambda : list occurrence) (cutformula : occurrence)
| ExchangeAdjacent (location : side) (position : nat)
| BacklinkExact (companion : judgment)
| BacklinkTags (renaming : list (nat * nat)) (companion : judgment)
| RotateLabels (original : judgment) (path : list bool) (rotate_left : bool)
| UnitLabels (original : judgment) (path : list bool) (on_left insert : bool).

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
    | Instantiate _ _ t, OnLeft, All u body => guard (term_wfb t) (fun _ => guard (pureb body) (fun Hp =>
        verified_build (left_conclusion pre post j.(succedent) (Occ l (All u body) None))
          (left_targets pre post j.(succedent) [[Occ l (subst_fo u t body) None]])
          (fun Hs Ht => universal_left pre post j.(succedent) l u body t Hp Hs Ht)))
    | Instantiate _ _ t, OnRight, Ex u body => guard (term_wfb t) (fun _ => guard (pureb body) (fun Hp =>
        verified_build (right_conclusion j.(antecedent) pre post (Occ l (Ex u body) None))
          (right_targets j.(antecedent) pre post [[Occ l (subst_fo u t body) None]])
          (fun Hs Ht => existential_right j.(antecedent) pre post l u body t Hp Hs Ht)))
    | Eigen _ _ v, OnRight, All u body => guard (pureb body) (fun Hp =>
        guard (eigen_freshb v (Jdg j.(antecedent) (pre ++ post)) l body) (fun Hfresh =>
          verified_build (right_conclusion j.(antecedent) pre post (Occ l (All u body) None))
            [right_conclusion j.(antecedent) pre post (Occ l (subst_fo u (Var v) body) None)]
            (fun Hs Ht => universal_right j.(antecedent) pre post l u v body Hp Hfresh Hs (Forall_inv Ht))))
    | Eigen _ _ v, OnLeft, Ex u body => guard (pureb body) (fun Hp =>
        guard (eigen_freshb v (Jdg (pre ++ post) j.(succedent)) l body) (fun Hfresh =>
          verified_build (left_conclusion pre post j.(succedent) (Occ l (Ex u body) None))
            [left_conclusion pre post j.(succedent) (Occ l (subst_fo u (Var v) body) None)]
            (fun Hs Ht => existential_left pre post j.(succedent) l u v body Hp Hfresh Hs (Forall_inv Ht))))
    | _, _, _ => None
    end
  end.

(** The common requests are translated literally; FOPL adds only binders
    and deterministic assignment candidates. *)
Definition shared_request request : option Common.rule_request :=
  match request with
  | Local loc n name => Some (Common.Local loc n name)
  | Weaken loc n => Some (Common.Weaken loc n)
  | Instantiate _ _ _ | Eigen _ _ _ => None
  | SubstituteWorld original x u => Some (Common.SubstituteWorld original x u)
  | SubstituteTrace original x l => Some (Common.SubstituteTrace original x l)
  | Cut gamma sigma delta lambda cut => Some (Common.Cut gamma sigma delta lambda cut)
  | ExchangeAdjacent loc n => Some (Common.ExchangeAdjacent loc n)
  | BacklinkExact companion => Some (Common.BacklinkExact companion)
  | BacklinkTags renaming companion => Some (Common.BacklinkTags renaming companion)
  | RotateLabels original path direction => Some (Common.RotateLabels original path direction)
  | UnitLabels original path on_left insert => Some (Common.UnitLabels original path on_left insert)
  end.
Definition raw_requested j request :=
  match request with
  | Local loc n _ | Instantiate loc n _ | Eigen loc n _ => requested_at j loc n request
  | _ => match shared_request request with
    | Some common => Common.raw_requested j.(relations) j common
    | None => None end
  end.
Definition generate_requested j request :=
  match request with
  | BacklinkTags renaming companion =>
      if judgment_eqb (rename_tags (rename_lookup renaming) j) companion
      then ensure_rule j (raw_requested j request) else None
  | _ => ensure_rule j (raw_requested j request)
  end.

Theorem generate_requested_spec j request r : generate_requested j request = Some r ->
  r.(Cyclic.rule_conclusion) = j /\ judgment_wfb j = true /\
  Forall (fun p => judgment_wfb p.(Cyclic.premise_judgment) = true /\
    Cyclic.edge_info_wfb j p.(Cyclic.premise_judgment) p.(Cyclic.premise_edge) = true) r.(Cyclic.rule_premises).
Proof.
  unfold generate_requested; destruct request; try apply ensure_rule_spec.
  destruct (judgment_eqb _ _); [apply ensure_rule_spec|discriminate].
Qed.
End MakeRuleGeneration.
