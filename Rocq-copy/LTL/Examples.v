From Stdlib Require Import List Bool Arith Lia String.
From Stdlib Require Import Logic.Classical_Pred_Type.

From CyclistRocq.LTL Require Import Syntax Rules.

Import ListNotations.
Open Scope string_scope.

(* ===== Overview =====
   Two worked cyclic proofs, built with the generic [Cyclic] framework:
   (1) [em_root]     : p ∨ ¬p   (excluded middle, no cycle)
   (2) [cyclic_root] : ◇p ∨ □¬p   (needs a backlink / cycle)
   For each we (a) define the judgments (nodes), (b) define the rule
   instances with their soundness proofs, (c) assemble a proof graph,
   (d) supply a trace witness, (e) prove the checker's side conditions
   and bundle them in a certificate, and (f) conclude [Valid].
   Finally some negative tests show the checker rejects bad graphs. *)

(* ---- Basic formulae ----
   [p] is the atom p. *)
Definition p : formula := Atom "p".
(* [np] is ¬p. *)
Definition np : formula := NegAtom "p".
(* [fp] is ◇p ("p eventually holds"). *)
Definition fp : formula := Eventually p.
(* [gnp] is □¬p ("p never holds"). *)
Definition gnp : formula := Always np.

(* ---- Edge infos ----
   An edge between two proof nodes lists (edge_valid) tag pairs (a,b):
   tag a of the conclusion is "followed" by tag b of the premise, with
   rank(b) <= rank(a); and (edge_progress) the sub-list where the rank
   strictly decreases.  A cycle is accepted only if some tag progresses.

   [empty_edge]: no tags followed.  Used for rules whose premises carry
   no tracked formula (Disj, the axiom branch). *)
Definition empty_edge : Cyclic.edge_info :=
  {| Cyclic.edge_valid := []; Cyclic.edge_progress := [] |}.

(* Tag 0 followed to tag 0, no strict decrease.
   Used by Eventually and by the backlink. *)
Definition stay0 : Cyclic.edge_info :=
  {| Cyclic.edge_valid := [(0, 0)]; Cyclic.edge_progress := [] |}.

(* Tag 0 -> tag 1 with strict rank decrease: □¬p (rank 2d+1) becomes
   ◯□¬p (rank 2d'+2) after unfolding Always. *)
Definition progress01 : Cyclic.edge_info :=
  {| Cyclic.edge_valid := [(0, 1)]; Cyclic.edge_progress := [(0, 1)] |}.

(* Tag 1 -> tag 0 with strict decrease: ◯□¬p moves to □¬p one step
   later, via the Next rule. *)
Definition progress10 : Cyclic.edge_info :=
  {| Cyclic.edge_valid := [(1, 0)]; Cyclic.edge_progress := [(1, 0)] |}.

(* ---- Judgments (proof nodes) ----
   Proof 1, excluded middle.  Root sequent: [p ∨ ¬p]. *)
Definition em_root : judgment := [untagged (Disj p np)].
(* Premise after the Disj rule: [p, ¬p] -- closed by the axiom rule. *)
Definition em_leaf : judgment := [untagged p; untagged np].

(* Proof 2 root: [◇p ∨ □¬p].  Valid: p occurs sometime, or never. *)
Definition cyclic_root : judgment :=
  [untagged (Disj fp gnp)].

(* [◇p, □¬p#0] -- the backlink target (the "companion" of the cycle).
   □¬p carries tag 0 so progress on it can be traced around the loop. *)
Definition cycle_companion : judgment :=
  [untagged fp; tagged 0 gnp].

(* After unfolding ◇p: [p, ◯◇p, □¬p#0]. *)
Definition after_eventually : judgment :=
  [untagged p; untagged (Next fp); tagged 0 gnp].

(* Left branch of the Always rule: [p, ¬p, ◯◇p] -- closed by Axiom
   (¬p is the unfolded head of □¬p). *)
Definition axiom_branch : judgment :=
  [untagged p; untagged np; untagged (Next fp)].

(* Right branch of the Always rule: [p, ◯◇p, ◯□¬p#1].  The Next rule
   strips the ◯'s and gives back [cycle_companion]. *)
Definition temporal_branch : judgment :=
  [untagged p; untagged (Next fp); tagged 1 (Next gnp)].

(* ---- Countermodel steps (one per proof edge) ----
   The framework proves soundness by contraposition: if the conclusion
   is false at a world, some premise is false at a related world.  These
   lemmas show it for each rule use.
   Here: if [p ∨ ¬p] is false, then [p, ¬p] is false. *)
Lemma em_counter_step w :
  ~ denote em_root w -> ~ denote em_leaf w.
Proof.
  intros Hroot Hleaf. apply Hroot.
  destruct Hleaf as [o [[Ho | [Ho | []]] Heval]]; subst o; cbn in Heval |- *.
  - exists (untagged (Disj p np)). split; [now left|now left].
  - exists (untagged (Disj p np)). split; [now left|now right].
Qed.

(* Disj step: falsity of [◇p ∨ □¬p] gives falsity of [cycle_companion]. *)
Lemma disj_counter_step w :
  ~ denote cyclic_root w -> ~ denote cycle_companion w.
Proof.
  intros Hroot Hpremise. apply Hroot.
  destruct Hpremise as [o [[Ho | [Ho | []]] Heval]]; subst o; cbn in Heval |- *.
  - exists (untagged (Disj fp gnp)). split; [now left|now left].
  - exists (untagged (Disj fp gnp)). split; [now left|now right].
Qed.

(* Eventually step: falsity of [cycle_companion] gives falsity of
   [after_eventually] at the same world (◇p unfolds to p ∨ ◯◇p). *)
Lemma eventually_counter_step w :
  ~ denote cycle_companion w -> ~ denote after_eventually w.
Proof.
  destruct w as [tr now]. intros Hsource Htarget. apply Hsource.
  destruct Htarget as [o [[Ho | [Ho | [Ho | []]]] Heval]];
    subst o; cbn in Heval |- *.
  - exists (untagged fp). split; [now left|].
    exists 0. now rewrite Nat.add_0_r.
  - exists (untagged fp). split; [now left|].
    destruct Heval as [k Hk]. exists (S k).
    cbn.
    replace (now + S k) with (S (now + k)) by lia. exact Hk.
  - exists (tagged 0 gnp). split; [right; now left|exact Heval].
Qed.

(* Helper: if [after_eventually] is false, then p is false at [now]. *)
Lemma p_is_false_under_after_eventually tr now :
  ~ denote after_eventually (tr, now) -> tr now "p" = false.
Proof.
  intro Hfalse. destruct (tr now "p") eqn:Hp; [|reflexivity].
  exfalso. apply Hfalse. exists (untagged p).
  split; [now left|exact Hp].
Qed.

(* Helper: if [after_eventually] is false, then □¬p is false at [now]. *)
Lemma gnp_is_false_under_after_eventually tr now :
  ~ denote after_eventually (tr, now) -> ~ eval gnp tr now.
Proof.
  intros Hfalse Hg. apply Hfalse.
  exists (tagged 0 gnp). split; [right; right; now left|exact Hg].
Qed.

(* Always step (right branch): falsity of [after_eventually] gives
   falsity of [temporal_branch] at the same world. *)
Lemma always_counter_step tr now :
  ~ denote after_eventually (tr, now) ->
  ~ denote temporal_branch (tr, now).
Proof.
  intros Hsource Htarget.
  pose proof (p_is_false_under_after_eventually tr now Hsource) as Hp.
  apply Hsource.
  destruct Htarget as [o [[Ho | [Ho | [Ho | []]]] Heval]];
    subst o; cbn in Heval |- *.
  - exists (untagged p). split; [now left|exact Heval].
  - exists (untagged (Next fp)). split; [right; now left|exact Heval].
  - exists (tagged 0 gnp). split; [right; right; now left|].
    intro k. destruct k as [|k].
    + rewrite Nat.add_0_r. exact Hp.
    + cbn. replace (now + S k) with (S (now + k)) by lia. apply Heval.
Qed.

(* Next step: falsity of [temporal_branch] at [now] gives falsity of
   [cycle_companion] at the NEXT world [now+1]. *)
Lemma next_counter_step tr now :
  ~ denote temporal_branch (tr, now) ->
  ~ denote cycle_companion (tr, S now).
Proof.
  intros Hsource Htarget. apply Hsource.
  destruct Htarget as [o [[Ho | [Ho | []]] Heval]];
    subst o; cbn in Heval |- *.
  - exists (untagged (Next fp)). split; [right; now left|exact Heval].
  - exists (tagged 1 (Next gnp)).
    split; [right; right; now left|exact Heval].
Qed.

(* ---- Edge-respect lemmas ----
   [respects_edge] says the rank inequalities promised by an edge_info
   really hold between the two worlds.
   Eventually edge: tag 0 keeps its rank (<=); no progress pairs. *)
Lemma stay0_eventually_respects w :
  Cyclic.respects_edge cycle_companion after_eventually w w stay0.
Proof.
  split.
  - intros a b Hin. cbn in Hin. destruct Hin as [Hin | []].
    inversion Hin; subst a b. apply Nat.le_refl.
  - intros a b Hin. inversion Hin.
Qed.

(* Always edge: rank of ◯□¬p#1 (2*d(now+1)+2) is strictly below the
   rank of □¬p#0 (2*d(now)+1), using [failure_distance_shift]. *)
Lemma progress01_always_respects tr now :
  ~ denote after_eventually (tr, now) ->
  Cyclic.respects_edge after_eventually temporal_branch
    (tr, now) (tr, now) progress01.
Proof.
  intro Hfalse.
  pose proof (p_is_false_under_after_eventually tr now Hfalse) as Hnp.
  pose proof (gnp_is_false_under_after_eventually tr now Hfalse) as Hnotg.
  assert (Hex : failure_exists np tr now).
  {
    unfold gnp in Hnotg. cbn in Hnotg.
    apply not_all_ex_not. exact Hnotg.
  }
  pose proof (failure_distance_shift np tr now Hnp Hex) as Hshift.
  split.
  - intros a b Hin. cbn in Hin. destruct Hin as [Hin | []].
    inversion Hin; subst a b.
    change (2 * failure_distance np tr (S now) + 2 <=
            2 * failure_distance np tr now + 1).
    lia.
  - intros a b Hin. cbn in Hin. destruct Hin as [Hin | []].
    inversion Hin; subst a b.
    change (2 * failure_distance np tr (S now) + 2 <
            2 * failure_distance np tr now + 1).
    lia.
Qed.

(* Next edge: rank of □¬p#0 at now+1 (2d+1) is strictly below that of
   ◯□¬p#1 at now (2d+2). *)
Lemma progress10_next_respects tr now :
  Cyclic.respects_edge temporal_branch cycle_companion
    (tr, now) (tr, S now) progress10.
Proof.
  split.
  - intros a b Hin. cbn in Hin. destruct Hin as [Hin | []].
    inversion Hin; subst a b.
    change (2 * failure_distance np tr (S now) + 1 <=
            2 * failure_distance np tr (S now) + 2). lia.
  - intros a b Hin. cbn in Hin. destruct Hin as [Hin | []].
    inversion Hin; subst a b.
    change (2 * failure_distance np tr (S now) + 1 <
            2 * failure_distance np tr (S now) + 2). lia.
Qed.

(* ---- Concrete rule soundness ----
   Soundness of the Always rule specialised to these judgments (validity
   of both branches implies validity of [after_eventually]). *)
Lemma always_concrete_rule :
  Cyclic.Valid axiom_branch ->
  Cyclic.Valid temporal_branch ->
  Cyclic.Valid after_eventually.
Proof.
  intros Hleft Hright [tr now].
  specialize (Hleft (tr, now)). specialize (Hright (tr, now)).
  destruct Hleft as [o [[Ho | [Ho | [Ho | []]]] Heval]];
    subst o; cbn in Heval |- *.
  - exists (untagged p). split; [now left|exact Heval].
  - destruct Hright as [o [[Ho | [Ho | [Ho | []]]] Hright_eval]];
      subst o; cbn in Hright_eval |- *.
    + exfalso. rewrite Heval in Hright_eval. discriminate.
    + exists (untagged (Next fp)).
      split; [right; now left|exact Hright_eval].
    + exists (tagged 0 gnp). split; [right; right; now left|].
      intro k. destruct k as [|k].
      * now rewrite Nat.add_0_r.
      * cbn. replace (now + S k) with (S (now + k)) by lia.
        apply Hright_eval.
  - exists (untagged (Next fp)). split; [right; now left|exact Heval].
Qed.

(* Soundness of the Next rule here: validity of [cycle_companion]
   implies validity of [temporal_branch]. *)
Lemma next_concrete_rule :
  Cyclic.Valid cycle_companion -> Cyclic.Valid temporal_branch.
Proof.
  intros Hvalid [tr now]. specialize (Hvalid (tr, S now)).
  destruct Hvalid as [o [[Ho | [Ho | []]] Heval]];
    subst o; cbn in Heval |- *.
  - exists (untagged (Next fp)). split; [right; now left|exact Heval].
  - exists (tagged 1 (Next gnp)).
    split; [right; right; now left|exact Heval].
Qed.

(* ---- Rule instances ----
   Each instance = name + conclusion + premises (with edges) + proofs that
   (1) valid premises give a valid conclusion, and (2) a countermodel step
   exists with the edge respected.
   Premise of the Disj rule in proof 1. *)
Definition em_disj_premise : Cyclic.premise :=
  {| Cyclic.premise_judgment := em_leaf;
     Cyclic.premise_edge := empty_edge |}.

(* Disj rule instance for proof 1: [p ∨ ¬p] from [p, ¬p]. *)
Definition em_disj_instance : Cyclic.rule_instance.
Proof.
  refine
    {| Cyclic.rule_name := "Disj";
       Cyclic.rule_conclusion := em_root;
       Cyclic.rule_premises := [em_disj_premise] |}.
  - intro H. apply disjunction_rule with (gamma := []) (ta := None) (tb := None).
    apply H with (p := em_disj_premise). now left.
  - intros w Hfalse. exists 0, em_disj_premise, w.
    split; [reflexivity|]. split; [now apply em_counter_step|].
    split; intros a b Hin; inversion Hin.
Defined.

(* Premise of the Disj rule in proof 2. *)
Definition disj_premise : Cyclic.premise :=
  {| Cyclic.premise_judgment := cycle_companion;
     Cyclic.premise_edge := empty_edge |}.

(* Disj rule instance for proof 2: [◇p ∨ □¬p] from [cycle_companion]. *)
Definition disj_instance : Cyclic.rule_instance.
Proof.
  refine
    {| Cyclic.rule_name := "Disj";
       Cyclic.rule_conclusion := cyclic_root;
       Cyclic.rule_premises := [disj_premise] |}.
  - intro H. apply disjunction_rule with (gamma := []) (ta := None)
      (tb := Some 0).
    apply H with (p := disj_premise). now left.
  - intros w Hfalse. exists 0, disj_premise, w.
    split; [reflexivity|]. split; [now apply disj_counter_step|].
    split; intros a b Hin; inversion Hin.
Defined.

(* Premise of the Eventually rule (edge [stay0]). *)
Definition eventually_premise : Cyclic.premise :=
  {| Cyclic.premise_judgment := after_eventually;
     Cyclic.premise_edge := stay0 |}.

(* Eventually rule: [cycle_companion] from [after_eventually]. *)
Definition eventually_instance : Cyclic.rule_instance.
Proof.
  refine
    {| Cyclic.rule_name := "Eventually";
       Cyclic.rule_conclusion := cycle_companion;
       Cyclic.rule_premises := [eventually_premise] |}.
  - intro H. apply eventually_rule with (gamma := [tagged 0 gnp])
      (ta := None).
    apply H with (p := eventually_premise). now left.
  - intros w Hfalse. exists 0, eventually_premise, w.
    split; [reflexivity|]. split; [now apply eventually_counter_step|].
    now apply stay0_eventually_respects.
Defined.

(* Left premise of the Always rule: [axiom_branch], no tag edge. *)
Definition always_left_premise : Cyclic.premise :=
  {| Cyclic.premise_judgment := axiom_branch;
     Cyclic.premise_edge := empty_edge |}.

(* Right premise of the Always rule: [temporal_branch], edge [progress01]. *)
Definition always_right_premise : Cyclic.premise :=
  {| Cyclic.premise_judgment := temporal_branch;
     Cyclic.premise_edge := progress01 |}.

(* Always rule (two premises): [after_eventually] from
   [axiom_branch] and [temporal_branch]. *)
Definition always_instance : Cyclic.rule_instance.
Proof.
  refine
    {| Cyclic.rule_name := "Always";
       Cyclic.rule_conclusion := after_eventually;
       Cyclic.rule_premises := [always_left_premise; always_right_premise] |}.
  - intro H. apply always_concrete_rule.
    + apply H with (p := always_left_premise). now left.
    + apply H with (p := always_right_premise). right; now left.
  - intros [tr now] Hfalse.
    exists 1, always_right_premise, (tr, now).
    split; [reflexivity|]. split; [now apply always_counter_step|].
    now apply progress01_always_respects.
Defined.

(* Premise of the Next rule: [cycle_companion], edge [progress10]. *)
Definition next_premise : Cyclic.premise :=
  {| Cyclic.premise_judgment := cycle_companion;
     Cyclic.premise_edge := progress10 |}.

(* Next rule: [temporal_branch] from [cycle_companion]. *)
Definition next_instance : Cyclic.rule_instance.
Proof.
  refine
    {| Cyclic.rule_name := "Next";
       Cyclic.rule_conclusion := temporal_branch;
       Cyclic.rule_premises := [next_premise] |}.
  - intro H. apply next_concrete_rule.
    apply H with (p := next_premise). now left.
  - intros [tr now] Hfalse.
    exists 0, next_premise, (tr, S now).
    split; [reflexivity|]. split; [now apply next_counter_step|].
    apply progress10_next_respects.
Defined.

(* Axiom instance closing [axiom_branch], with context [◯◇p]. *)
Definition branch_axiom : Cyclic.axiom_instance :=
  atom_axiom_instance [untagged (Next fp)] "p".

(* Axiom instance closing [em_leaf], with empty context. *)
Definition em_axiom : Cyclic.axiom_instance :=
  atom_axiom_instance [] "p".

(* The backlink rule instance targeting [cycle_companion]. *)
Definition cycle_backlink : Cyclic.rule_instance :=
  exact_backlink_instance cycle_companion.

(* ---- Proof graphs ----
   A graph is a root plus numbered nodes; each node has a judgment and a
   payload (RuleNode inst children / AxiomNode inst / BacklinkNode inst target).
   Proof 1: node 0 (Disj) -> node 1 (axiom). *)
Definition em_graph : Cyclic.graph :=
  {| Cyclic.graph_root := em_root;
     Cyclic.graph_nodes :=
       [{| Cyclic.node_judgment := em_root;
           Cyclic.node_payload := Cyclic.RuleNode em_disj_instance [1] |};
        {| Cyclic.node_judgment := em_leaf;
           Cyclic.node_payload := Cyclic.AxiomNode em_axiom |}] |}.

(* Proof 2, nodes by index:
     0 cyclic_root      (Disj)       -> 1
     1 cycle_companion  (Eventually) -> 2
     2 after_eventually (Always)     -> 3, 4
     3 axiom_branch     (Axiom)
     4 temporal_branch  (Next)       -> 5
     5 cycle_companion  (Backlink to node 1)  -- closes the cycle *)
Definition cyclic_graph : Cyclic.graph :=
  {| Cyclic.graph_root := cyclic_root;
     Cyclic.graph_nodes :=
       [{| Cyclic.node_judgment := cyclic_root;
           Cyclic.node_payload := Cyclic.RuleNode disj_instance [1] |};
        {| Cyclic.node_judgment := cycle_companion;
           Cyclic.node_payload := Cyclic.RuleNode eventually_instance [2] |};
        {| Cyclic.node_judgment := after_eventually;
           Cyclic.node_payload := Cyclic.RuleNode always_instance [3; 4] |};
        {| Cyclic.node_judgment := axiom_branch;
           Cyclic.node_payload := Cyclic.AxiomNode branch_axiom |};
        {| Cyclic.node_judgment := temporal_branch;
           Cyclic.node_payload := Cyclic.RuleNode next_instance [5] |};
        {| Cyclic.node_judgment := cycle_companion;
           Cyclic.node_payload := Cyclic.BacklinkNode cycle_backlink 1 |}] |}.

(* ---- Scripts ----
   The same graphs, built command by command by the framework's builder
   (ApplyRule on an open node, CloseWith an axiom, AddBacklink from a node
   to an ancestor).  Script for proof 1. *)
Definition em_script : list Cyclic.command :=
  [Cyclic.ApplyRule 0 em_disj_instance;
   Cyclic.CloseWith 1 em_axiom].

(* Script for proof 2; the last command adds the backlink 5 -> 1. *)
Definition cyclic_script : list Cyclic.command :=
  [Cyclic.ApplyRule 0 disj_instance;
   Cyclic.ApplyRule 1 eventually_instance;
   Cyclic.ApplyRule 2 always_instance;
   Cyclic.CloseWith 3 branch_axiom;
   Cyclic.ApplyRule 4 next_instance;
   Cyclic.AddBacklink 5 1 cycle_backlink].

(* Running the script succeeds and yields exactly [em_graph]. *)
Example em_builder_records_whole_graph :
  (Cyclic.run_script em_root em_script).(Cyclic.build_ok) = true /\
  (Cyclic.run_script em_root em_script).(Cyclic.built_graph) = em_graph.
Proof. vm_compute. auto. Qed.

(* Running the script succeeds and yields exactly [cyclic_graph]. *)
Example cyclic_builder_records_whole_graph :
  (Cyclic.run_script cyclic_root cyclic_script).(Cyclic.build_ok) = true /\
  (Cyclic.run_script cyclic_root cyclic_script).(Cyclic.built_graph) = cyclic_graph.
Proof. vm_compute. auto. Qed.

(* ---- Trace witnesses ----
   A witness chooses, per node, which tag (if any) is traced along an
   infinite path, and a natural-number potential used to check progress.
   Proof 1 has no cycle, so nothing is traced. *)
Definition em_witness : Cyclic.trace_witness :=
  {| Cyclic.witness_tag := fun _ => None;
     Cyclic.witness_potential := fun _ => 0 |}.

(* Proof 2: the traced formula is □¬p: tag 0 at nodes 1,2,5 and tag 1
   (◯□¬p) at node 4; untraced elsewhere. *)
Definition cycle_witness_tag (i : nat) : option nat :=
  match i with
  | 1 | 2 | 5 => Some 0
  | 4 => Some 1
  | _ => None
  end.

(* Potentials along the cycle 1 -> 2 -> 4 -> 5 -> 1; they let the checker
   verify the cycle contains a strict progress step. *)
Definition cycle_witness_potential (i : nat) : nat :=
  match i with
  | 1 => 1
  | 5 => 2
  | _ => 0
  end.

(* Bundle of tag and potential for proof 2. *)
Definition cycle_witness : Cyclic.trace_witness :=
  {| Cyclic.witness_tag := cycle_witness_tag;
     Cyclic.witness_potential := cycle_witness_potential |}.

(* The boolean checker (structure + relations + witness) accepts proof 1. *)
Example em_raw_check_passes :
  Cyclic.raw_check em_graph em_witness = true.
Proof. vm_compute. reflexivity. Qed.

(* ...and proof 2. *)
Example cyclic_raw_check_passes :
  Cyclic.raw_check cyclic_graph cycle_witness = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- Edge facts for the certificate ----
   [edge_at g i j e]: graph [g] has an edge i -> j carrying info [e].
   One lemma per edge of [cyclic_graph]. *)
Lemma cyclic_edge_0_1 :
  Cyclic.edge_at cyclic_graph 0 1 empty_edge.
Proof. eexists; split; [reflexivity|]. cbn. now left. Qed.

Lemma cyclic_edge_1_2 :
  Cyclic.edge_at cyclic_graph 1 2 stay0.
Proof. eexists; split; [reflexivity|]. cbn. now left. Qed.

Lemma cyclic_edge_2_3 :
  Cyclic.edge_at cyclic_graph 2 3 empty_edge.
Proof. eexists; split; [reflexivity|]. cbn. now left. Qed.

Lemma cyclic_edge_2_4 :
  Cyclic.edge_at cyclic_graph 2 4 progress01.
Proof. eexists; split; [reflexivity|]. cbn. right; now left. Qed.

Lemma cyclic_edge_4_5 :
  Cyclic.edge_at cyclic_graph 4 5 progress10.
Proof. eexists; split; [reflexivity|]. cbn. now left. Qed.

(* Backlink edge 5 -> 1 uses the premise edge of [exact_backlink_premise]. *)
Lemma cyclic_edge_5_1 :
  Cyclic.edge_at cyclic_graph 5 1
    (Cyclic.premise_edge (exact_backlink_premise cycle_companion)).
Proof. eexists; split; [reflexivity|]. cbn. now left. Qed.

(* That backlink edge is literally [stay0] (identity on tag 0). *)
Lemma backlink_stay0 :
  Cyclic.premise_edge (exact_backlink_premise cycle_companion) = stay0.
Proof. reflexivity. Qed.

(* The backlink edge respects ranks: same judgment, same world. *)
Lemma stay0_backlink_respects w :
  Cyclic.respects_edge cycle_companion cycle_companion w w stay0.
Proof.
  split.
  - intros a b Hin. cbn in Hin. destruct Hin as [Hin | []].
    inversion Hin; subst a b. apply Nat.le_refl.
  - intros a b Hin. inversion Hin.
Qed.

(* Edge 0 -> 1 in [em_graph]. *)
Lemma em_edge_0_1 : Cyclic.edge_at em_graph 0 1 empty_edge.
Proof. eexists; split; [reflexivity|]. cbn. now left. Qed.

(* [p ∨ ¬p] can never be false (case split on the atom). *)
Lemma em_false_impossible tr now : ~ denote em_root (tr, now) -> False.
Proof.
  intro Hfalse. apply Hfalse.
  destruct (tr now "p") eqn:Hp.
  - exists (untagged (Disj p np)). split; [now left|now left].
  - exists (untagged (Disj p np)). split; [now left|now right].
Qed.

(* [axiom_branch] can never be false: it contains p and ¬p. *)
Lemma axiom_branch_false_impossible tr now :
  ~ denote axiom_branch (tr, now) -> False.
Proof.
  intro Hfalse. apply Hfalse.
  destruct (tr now "p") eqn:Hp.
  - exists (untagged p). split; [now left|exact Hp].
  - exists (untagged np). split; [right; now left|exact Hp].
Qed.

(* [em_leaf] can never be false either. *)
Lemma em_leaf_false_impossible tr now :
  ~ denote em_leaf (tr, now) -> False.
Proof.
  intro Hfalse. apply Hfalse.
  destruct (tr now "p") eqn:Hp.
  - exists (untagged p). split; [now left|exact Hp].
  - exists (untagged np). split; [right; now left|exact Hp].
Qed.

(* ---- Certificate obligations ----
   A node is "live" if it can start an infinite path.  If a node is false
   at some world it must be live; axiom nodes are never false, so they
   need not be.  Proof 2 version. *)
Lemma cyclic_false_nodes_are_live i w :
  i < List.length cyclic_graph.(Cyclic.graph_nodes) ->
  ~ Cyclic.holds (Cyclic.label_at cyclic_graph i) w ->
  Cyclic.liveb cyclic_graph i = true.
Proof.
  destruct w as [tr now]. intros Hi Hfalse.
  destruct i as [|[|[|[|[|[|i]]]]]].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exfalso. apply (axiom_branch_false_impossible tr now).
    exact Hfalse.
  - reflexivity.
  - reflexivity.
  - cbn in Hi. lia.
Qed.

(* Same obligation for proof 1. *)
Lemma em_false_nodes_are_live i w :
  i < List.length em_graph.(Cyclic.graph_nodes) ->
  ~ Cyclic.holds (Cyclic.label_at em_graph i) w ->
  Cyclic.liveb em_graph i = true.
Proof.
  destruct w as [tr now]. intros Hi Hfalse.
  destruct i as [|[|i]].
  - exfalso. now apply (em_false_impossible tr now).
  - exfalso. now apply (em_leaf_false_impossible tr now).
  - cbn in Hi. lia.
Qed.

(* Advance: from any false node there is an edge to a successor that is
   false at a related world and respects the edge.  This builds the
   infinite countermodel path in the soundness argument.  Proof 2. *)
Lemma cyclic_advance :
  forall i w,
    i < List.length cyclic_graph.(Cyclic.graph_nodes) ->
    ~ Cyclic.holds (Cyclic.label_at cyclic_graph i) w ->
    { j : nat &
      { w' : world &
        { e : Cyclic.edge_info |
          Cyclic.edge_at cyclic_graph i j e /\
          j < List.length cyclic_graph.(Cyclic.graph_nodes) /\
          ~ Cyclic.holds (Cyclic.label_at cyclic_graph j) w' /\
          Cyclic.respects_edge
            (Cyclic.label_at cyclic_graph i)
            (Cyclic.label_at cyclic_graph j) w w' e } } }.
Proof.
  intros i [tr now] Hi Hfalse.
  destruct i as [|[|[|[|[|[|i]]]]]].
  - exists 1, (tr, now), empty_edge.
    split; [exact cyclic_edge_0_1|].
    split; [cbn; lia|].
    split; [now apply disj_counter_step|].
    split; intros a b Hin; inversion Hin.
  - exists 2, (tr, now), stay0.
    split; [exact cyclic_edge_1_2|].
    split; [cbn; lia|].
    split; [now apply eventually_counter_step|].
    apply stay0_eventually_respects.
  - exists 4, (tr, now), progress01.
    split; [exact cyclic_edge_2_4|].
    split; [cbn; lia|].
    split; [now apply always_counter_step|].
    now apply progress01_always_respects.
  - exfalso. now apply (axiom_branch_false_impossible tr now).
  - exists 5, (tr, S now), progress10.
    split; [exact cyclic_edge_4_5|].
    split; [cbn; lia|].
    split; [now apply next_counter_step|].
    apply progress10_next_respects.
  - exists 1, (tr, now), stay0.
    split; [rewrite <- backlink_stay0; exact cyclic_edge_5_1|].
    split; [cbn; lia|].
    split; [exact Hfalse|].
    apply stay0_backlink_respects.
  - cbn in Hi. lia.
Qed.

(* Advance obligation for proof 1. *)
Lemma em_advance :
  forall i w,
    i < List.length em_graph.(Cyclic.graph_nodes) ->
    ~ Cyclic.holds (Cyclic.label_at em_graph i) w ->
    { j : nat &
      { w' : world &
        { e : Cyclic.edge_info |
          Cyclic.edge_at em_graph i j e /\
          j < List.length em_graph.(Cyclic.graph_nodes) /\
          ~ Cyclic.holds (Cyclic.label_at em_graph j) w' /\
          Cyclic.respects_edge
            (Cyclic.label_at em_graph i)
            (Cyclic.label_at em_graph j) w w' e } } }.
Proof.
  intros i [tr now] Hi Hfalse.
  destruct i as [|[|i]].
  - exists 1, (tr, now), empty_edge.
    split; [exact em_edge_0_1|].
    split; [cbn; lia|].
    split; [now apply em_counter_step|].
    split; intros a b Hin; inversion Hin.
  - exfalso. now apply (em_leaf_false_impossible tr now).
  - cbn in Hi. lia.
Qed.

(* Every edge into a live node is a legal step of [cycle_witness]: tags
   match the edge's pairs, and the potential does not increase (or the
   progress pair strictly decreases it). *)
Lemma cyclic_trace_transition :
  forall i j e,
    Cyclic.edge_at cyclic_graph i j e ->
    Cyclic.liveb cyclic_graph j = true ->
    Cyclic.trace_transition cycle_witness i j e.
Proof.
  intros i j e [n [Hnode Hedge]] Hlive.
  assert (Hi : i < List.length cyclic_graph.(Cyclic.graph_nodes)).
  {
    apply (proj1 (@nth_error_Some Cyclic.node
      cyclic_graph.(Cyclic.graph_nodes) i)).
    unfold Cyclic.node_at in Hnode. rewrite Hnode. discriminate.
  }
  destruct i as [|[|[|[|[|[|i]]]]]]; cbn in Hnode.
  - inversion Hnode; subst n. cbn in Hedge.
    destruct Hedge as [Hedge | []]. inversion Hedge; subst j e. exact I.
  - inversion Hnode; subst n. cbn in Hedge.
    destruct Hedge as [Hedge | []]. inversion Hedge; subst j e.
    cbn. split; [now left|right; lia].
  - inversion Hnode; subst n. cbn in Hedge.
    destruct Hedge as [Hedge | [Hedge | []]].
    + inversion Hedge; subst j e. vm_compute in Hlive. discriminate.
    + inversion Hedge; subst j e. cbn. split; [now left|left; now left].
  - inversion Hnode; subst n. inversion Hedge.
  - inversion Hnode; subst n. cbn in Hedge.
    destruct Hedge as [Hedge | []]. inversion Hedge; subst j e.
    cbn. split; [now left|left; now left].
  - inversion Hnode; subst n. cbn in Hedge.
    destruct Hedge as [Hedge | []]. inversion Hedge; subst j e.
    cbn. split; [now left|right; lia].
  - cbn in Hi. lia.
Qed.

(* Trace-transition obligation for proof 1 (the only edge leads to a
   non-live node, so it is vacuous). *)
Lemma em_trace_transition :
  forall i j e,
    Cyclic.edge_at em_graph i j e ->
    Cyclic.liveb em_graph j = true ->
    Cyclic.trace_transition em_witness i j e.
Proof.
  intros i j e [n [Hnode Hedge]] Hlive.
  assert (Hi : i < List.length em_graph.(Cyclic.graph_nodes)).
  {
    apply (proj1 (@nth_error_Some Cyclic.node
      em_graph.(Cyclic.graph_nodes) i)).
    unfold Cyclic.node_at in Hnode. rewrite Hnode. discriminate.
  }
  destruct i as [|[|i]]; cbn in Hnode.
  - inversion Hnode; subst n. cbn in Hedge.
    destruct Hedge as [Hedge | []]. inversion Hedge; subst j e.
    vm_compute in Hlive. discriminate.
  - inversion Hnode; subst n. inversion Hedge.
  - cbn in Hi. lia.
Qed.

(* ---- Certificates ----
   Bundle graph + witness + all semantic obligations proved above.
   [check_certificate] re-checks the boolean part, and
   [finish_cyclic_certificate] derives [Valid].
   Certificate for proof 1. *)
Definition em_certificate : Cyclic.certificate :=
  {| Cyclic.cert_graph := em_graph;
     Cyclic.cert_witness := em_witness;
     Cyclic.cert_root_bound := ltac:(cbn; lia);
     Cyclic.cert_root_label := eq_refl;
     Cyclic.cert_false_live := em_false_nodes_are_live;
     Cyclic.cert_advance := em_advance;
     Cyclic.cert_trace_transition := em_trace_transition |}.

(* Certificate for proof 2. *)
Definition ltl_cycle_certificate : Cyclic.certificate :=
  {| Cyclic.cert_graph := cyclic_graph;
     Cyclic.cert_witness := cycle_witness;
     Cyclic.cert_root_bound := ltac:(cbn; lia);
     Cyclic.cert_root_label := eq_refl;
     Cyclic.cert_false_live := cyclic_false_nodes_are_live;
     Cyclic.cert_advance := cyclic_advance;
     Cyclic.cert_trace_transition := cyclic_trace_transition |}.

(* The certificate for proof 1 passes the checker. *)
Example em_certificate_checks :
  Cyclic.check_certificate em_certificate = true.
Proof. vm_compute. reflexivity. Qed.

(* The certificate for proof 2 passes the checker. *)
Example ltl_cycle_certificate_checks :
  Cyclic.check_certificate ltl_cycle_certificate = true.
Proof. vm_compute. reflexivity. Qed.

(* Final theorem 1: p ∨ ¬p is valid, via the certificate. *)
Theorem excluded_middle_ltl : Cyclic.Valid em_root.
Proof. Cyclic.finish_cyclic_certificate em_certificate. Qed.

(* Final theorem 2: ◇p ∨ □¬p is valid.  A genuinely cyclic proof: the
   backlink is justified because □¬p's rank strictly decreases. *)
Theorem eventually_or_always_not : Cyclic.Valid cyclic_root.
Proof. Cyclic.finish_cyclic_certificate ltl_cycle_certificate. Qed.

(** Rejection tests exercise independent failure modes of the checker. *)
(* A graph with only the root and an open goal (no proof yet). *)
Definition open_graph : Cyclic.graph := Cyclic.start_graph em_root.

(* A graph with an open goal is rejected. *)
Example open_goal_is_rejected :
  Cyclic.raw_check open_graph em_witness = false.
Proof. vm_compute. reflexivity. Qed.

(* Proof 1 but the Disj node points to a non-existent child (index 99). *)
Definition dangling_graph : Cyclic.graph :=
  {| Cyclic.graph_root := em_root;
     Cyclic.graph_nodes :=
       [{| Cyclic.node_judgment := em_root;
           Cyclic.node_payload := Cyclic.RuleNode em_disj_instance [99] |};
        {| Cyclic.node_judgment := em_leaf;
           Cyclic.node_payload := Cyclic.AxiomNode em_axiom |}] |}.

(* Dangling child pointers are rejected. *)
Example dangling_target_is_rejected :
  Cyclic.raw_check dangling_graph em_witness = false.
Proof. vm_compute. reflexivity. Qed.

(* An edge whose progress pair (7,8) is not among its valid pairs. *)
Definition malformed_edge : Cyclic.edge_info :=
  {| Cyclic.edge_valid := [];
     Cyclic.edge_progress := [(7, 8)] |}.

(* Premise carrying the malformed edge. *)
Definition malformed_premise : Cyclic.premise :=
  {| Cyclic.premise_judgment := em_leaf;
     Cyclic.premise_edge := malformed_edge |}.

(* A semantically sound rule instance that uses the malformed premise. *)
Definition malformed_rule : Cyclic.rule_instance.
Proof.
  refine
    {| Cyclic.rule_name := "Malformed-test-rule";
       Cyclic.rule_conclusion := em_root;
       Cyclic.rule_premises := [malformed_premise] |}.
  - intros _. intros [tr now].
    destruct (tr now "p") eqn:Hp.
    + exists (untagged (Disj p np)). split; [now left|now left].
    + exists (untagged (Disj p np)). split; [now left|now right].
  - intros [tr now] Hfalse.
    exfalso. now apply (em_false_impossible tr now).
Defined.

(* Proof 1 with the malformed rule substituted. *)
Definition malformed_graph : Cyclic.graph :=
  {| Cyclic.graph_root := em_root;
     Cyclic.graph_nodes :=
       [{| Cyclic.node_judgment := em_root;
           Cyclic.node_payload := Cyclic.RuleNode malformed_rule [1] |};
        {| Cyclic.node_judgment := em_leaf;
           Cyclic.node_payload := Cyclic.AxiomNode em_axiom |}] |}.

(* The structural check rejects progress pairs not in edge_valid. *)
Example progress_must_be_valid_is_rejected :
  Cyclic.structural_check malformed_graph = false.
Proof. vm_compute. reflexivity. Qed.

(* A pure loop: node 0 (a rule) -> node 1 (backlink to 0), with no
   progress anywhere. *)
Definition flat_graph : Cyclic.graph :=
  {| Cyclic.graph_root := cycle_companion;
     Cyclic.graph_nodes :=
       [{| Cyclic.node_judgment := cycle_companion;
           Cyclic.node_payload :=
             Cyclic.RuleNode cycle_backlink [1] |};
        {| Cyclic.node_judgment := cycle_companion;
           Cyclic.node_payload :=
             Cyclic.BacklinkNode cycle_backlink 0 |}] |}.

(* The structure is well formed... *)
Example flat_graph_is_structurally_well_formed :
  Cyclic.structural_check flat_graph = true.
Proof. vm_compute. reflexivity. Qed.

(* ...but the relational check rejects it: no tag strictly decreases
   around the cycle (the essential soundness condition). *)
Example flat_cycle_without_progress_is_rejected :
  Cyclic.relational_check flat_graph = false.
Proof. vm_compute. reflexivity. Qed.
