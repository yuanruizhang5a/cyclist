From Stdlib Require Import List Bool Arith Lia String.
From Stdlib Require Import Logic.Classical_Pred_Type.

From CyclistRocq.LTL Require Import Syntax Rules.

Import ListNotations.
Open Scope string_scope.

Definition p : formula := Atom "p".
Definition np : formula := NegAtom "p".
Definition fp : formula := Eventually p.
Definition gnp : formula := Always np.

Definition empty_edge : Cyclic.edge_info :=
  {| Cyclic.edge_valid := []; Cyclic.edge_progress := [] |}.

Definition stay0 : Cyclic.edge_info :=
  {| Cyclic.edge_valid := [(0, 0)]; Cyclic.edge_progress := [] |}.

Definition progress01 : Cyclic.edge_info :=
  {| Cyclic.edge_valid := [(0, 1)]; Cyclic.edge_progress := [(0, 1)] |}.

Definition progress10 : Cyclic.edge_info :=
  {| Cyclic.edge_valid := [(1, 0)]; Cyclic.edge_progress := [(1, 0)] |}.

Definition em_root : judgment := [untagged (Disj p np)].
Definition em_leaf : judgment := [untagged p; untagged np].

Definition cyclic_root : judgment :=
  [untagged (Disj fp gnp)].

Definition cycle_companion : judgment :=
  [untagged fp; tagged 0 gnp].

Definition after_eventually : judgment :=
  [untagged p; untagged (Next fp); tagged 0 gnp].

Definition axiom_branch : judgment :=
  [untagged p; untagged np; untagged (Next fp)].

Definition temporal_branch : judgment :=
  [untagged p; untagged (Next fp); tagged 1 (Next gnp)].

Lemma em_counter_step w :
  ~ denote em_root w -> ~ denote em_leaf w.
Proof.
  intros Hroot Hleaf. apply Hroot.
  destruct Hleaf as [o [[Ho | [Ho | []]] Heval]]; subst o; cbn in Heval |- *.
  - exists (untagged (Disj p np)). split; [now left|now left].
  - exists (untagged (Disj p np)). split; [now left|now right].
Qed.

Lemma disj_counter_step w :
  ~ denote cyclic_root w -> ~ denote cycle_companion w.
Proof.
  intros Hroot Hpremise. apply Hroot.
  destruct Hpremise as [o [[Ho | [Ho | []]] Heval]]; subst o; cbn in Heval |- *.
  - exists (untagged (Disj fp gnp)). split; [now left|now left].
  - exists (untagged (Disj fp gnp)). split; [now left|now right].
Qed.

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

Lemma p_is_false_under_after_eventually tr now :
  ~ denote after_eventually (tr, now) -> tr now "p" = false.
Proof.
  intro Hfalse. destruct (tr now "p") eqn:Hp; [|reflexivity].
  exfalso. apply Hfalse. exists (untagged p).
  split; [now left|exact Hp].
Qed.

Lemma gnp_is_false_under_after_eventually tr now :
  ~ denote after_eventually (tr, now) -> ~ eval gnp tr now.
Proof.
  intros Hfalse Hg. apply Hfalse.
  exists (tagged 0 gnp). split; [right; right; now left|exact Hg].
Qed.

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

Lemma stay0_eventually_respects w :
  Cyclic.respects_edge cycle_companion after_eventually w w stay0.
Proof.
  split.
  - intros a b Hin. cbn in Hin. destruct Hin as [Hin | []].
    inversion Hin; subst a b. apply Nat.le_refl.
  - intros a b Hin. inversion Hin.
Qed.

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

Definition em_disj_premise : Cyclic.premise :=
  {| Cyclic.premise_judgment := em_leaf;
     Cyclic.premise_edge := empty_edge |}.

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

Definition disj_premise : Cyclic.premise :=
  {| Cyclic.premise_judgment := cycle_companion;
     Cyclic.premise_edge := empty_edge |}.

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

Definition eventually_premise : Cyclic.premise :=
  {| Cyclic.premise_judgment := after_eventually;
     Cyclic.premise_edge := stay0 |}.

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

Definition always_left_premise : Cyclic.premise :=
  {| Cyclic.premise_judgment := axiom_branch;
     Cyclic.premise_edge := empty_edge |}.

Definition always_right_premise : Cyclic.premise :=
  {| Cyclic.premise_judgment := temporal_branch;
     Cyclic.premise_edge := progress01 |}.

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

Definition next_premise : Cyclic.premise :=
  {| Cyclic.premise_judgment := cycle_companion;
     Cyclic.premise_edge := progress10 |}.

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

Definition branch_axiom : Cyclic.axiom_instance :=
  atom_axiom_instance [untagged (Next fp)] "p".

Definition em_axiom : Cyclic.axiom_instance :=
  atom_axiom_instance [] "p".

Definition cycle_backlink : Cyclic.rule_instance :=
  exact_backlink_instance cycle_companion.

Definition em_graph : Cyclic.graph :=
  {| Cyclic.graph_root := em_root;
     Cyclic.graph_nodes :=
       [{| Cyclic.node_judgment := em_root;
           Cyclic.node_payload := Cyclic.RuleNode em_disj_instance [1] |};
        {| Cyclic.node_judgment := em_leaf;
           Cyclic.node_payload := Cyclic.AxiomNode em_axiom |}] |}.

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

Definition em_script : list Cyclic.command :=
  [Cyclic.ApplyRule 0 em_disj_instance;
   Cyclic.CloseWith 1 em_axiom].

Definition cyclic_script : list Cyclic.command :=
  [Cyclic.ApplyRule 0 disj_instance;
   Cyclic.ApplyRule 1 eventually_instance;
   Cyclic.ApplyRule 2 always_instance;
   Cyclic.CloseWith 3 branch_axiom;
   Cyclic.ApplyRule 4 next_instance;
   Cyclic.AddBacklink 5 1 cycle_backlink].

Example em_builder_records_whole_graph :
  (Cyclic.run_script em_root em_script).(Cyclic.build_ok) = true /\
  (Cyclic.run_script em_root em_script).(Cyclic.built_graph) = em_graph.
Proof. vm_compute. auto. Qed.

Example cyclic_builder_records_whole_graph :
  (Cyclic.run_script cyclic_root cyclic_script).(Cyclic.build_ok) = true /\
  (Cyclic.run_script cyclic_root cyclic_script).(Cyclic.built_graph) = cyclic_graph.
Proof. vm_compute. auto. Qed.

Definition em_witness : Cyclic.trace_witness :=
  {| Cyclic.witness_tag := fun _ => None;
     Cyclic.witness_potential := fun _ => 0 |}.

Definition cycle_witness_tag (i : nat) : option nat :=
  match i with
  | 1 | 2 | 5 => Some 0
  | 4 => Some 1
  | _ => None
  end.

Definition cycle_witness_potential (i : nat) : nat :=
  match i with
  | 1 => 1
  | 5 => 2
  | _ => 0
  end.

Definition cycle_witness : Cyclic.trace_witness :=
  {| Cyclic.witness_tag := cycle_witness_tag;
     Cyclic.witness_potential := cycle_witness_potential |}.

Example em_raw_check_passes :
  Cyclic.raw_check em_graph em_witness = true.
Proof. vm_compute. reflexivity. Qed.

Example cyclic_raw_check_passes :
  Cyclic.raw_check cyclic_graph cycle_witness = true.
Proof. vm_compute. reflexivity. Qed.

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

Lemma cyclic_edge_5_1 :
  Cyclic.edge_at cyclic_graph 5 1
    (Cyclic.premise_edge (exact_backlink_premise cycle_companion)).
Proof. eexists; split; [reflexivity|]. cbn. now left. Qed.

Lemma backlink_stay0 :
  Cyclic.premise_edge (exact_backlink_premise cycle_companion) = stay0.
Proof. reflexivity. Qed.

Lemma stay0_backlink_respects w :
  Cyclic.respects_edge cycle_companion cycle_companion w w stay0.
Proof.
  split.
  - intros a b Hin. cbn in Hin. destruct Hin as [Hin | []].
    inversion Hin; subst a b. apply Nat.le_refl.
  - intros a b Hin. inversion Hin.
Qed.

Lemma em_edge_0_1 : Cyclic.edge_at em_graph 0 1 empty_edge.
Proof. eexists; split; [reflexivity|]. cbn. now left. Qed.

Lemma em_false_impossible tr now : ~ denote em_root (tr, now) -> False.
Proof.
  intro Hfalse. apply Hfalse.
  destruct (tr now "p") eqn:Hp.
  - exists (untagged (Disj p np)). split; [now left|now left].
  - exists (untagged (Disj p np)). split; [now left|now right].
Qed.

Lemma axiom_branch_false_impossible tr now :
  ~ denote axiom_branch (tr, now) -> False.
Proof.
  intro Hfalse. apply Hfalse.
  destruct (tr now "p") eqn:Hp.
  - exists (untagged p). split; [now left|exact Hp].
  - exists (untagged np). split; [right; now left|exact Hp].
Qed.

Lemma em_leaf_false_impossible tr now :
  ~ denote em_leaf (tr, now) -> False.
Proof.
  intro Hfalse. apply Hfalse.
  destruct (tr now "p") eqn:Hp.
  - exists (untagged p). split; [now left|exact Hp].
  - exists (untagged np). split; [right; now left|exact Hp].
Qed.

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

Definition em_certificate : Cyclic.certificate :=
  {| Cyclic.cert_graph := em_graph;
     Cyclic.cert_witness := em_witness;
     Cyclic.cert_root_bound := ltac:(cbn; lia);
     Cyclic.cert_root_label := eq_refl;
     Cyclic.cert_false_live := em_false_nodes_are_live;
     Cyclic.cert_advance := em_advance;
     Cyclic.cert_trace_transition := em_trace_transition |}.

Definition ltl_cycle_certificate : Cyclic.certificate :=
  {| Cyclic.cert_graph := cyclic_graph;
     Cyclic.cert_witness := cycle_witness;
     Cyclic.cert_root_bound := ltac:(cbn; lia);
     Cyclic.cert_root_label := eq_refl;
     Cyclic.cert_false_live := cyclic_false_nodes_are_live;
     Cyclic.cert_advance := cyclic_advance;
     Cyclic.cert_trace_transition := cyclic_trace_transition |}.

Example em_certificate_checks :
  Cyclic.check_certificate em_certificate = true.
Proof. vm_compute. reflexivity. Qed.

Example ltl_cycle_certificate_checks :
  Cyclic.check_certificate ltl_cycle_certificate = true.
Proof. vm_compute. reflexivity. Qed.

Theorem excluded_middle_ltl : Cyclic.Valid em_root.
Proof. Cyclic.finish_cyclic_certificate em_certificate. Qed.

Theorem eventually_or_always_not : Cyclic.Valid cyclic_root.
Proof. Cyclic.finish_cyclic_certificate ltl_cycle_certificate. Qed.

(** Rejection tests exercise independent failure modes of the checker. *)
Definition open_graph : Cyclic.graph := Cyclic.start_graph em_root.

Example open_goal_is_rejected :
  Cyclic.raw_check open_graph em_witness = false.
Proof. vm_compute. reflexivity. Qed.

Definition dangling_graph : Cyclic.graph :=
  {| Cyclic.graph_root := em_root;
     Cyclic.graph_nodes :=
       [{| Cyclic.node_judgment := em_root;
           Cyclic.node_payload := Cyclic.RuleNode em_disj_instance [99] |};
        {| Cyclic.node_judgment := em_leaf;
           Cyclic.node_payload := Cyclic.AxiomNode em_axiom |}] |}.

Example dangling_target_is_rejected :
  Cyclic.raw_check dangling_graph em_witness = false.
Proof. vm_compute. reflexivity. Qed.

Definition malformed_edge : Cyclic.edge_info :=
  {| Cyclic.edge_valid := [];
     Cyclic.edge_progress := [(7, 8)] |}.

Definition malformed_premise : Cyclic.premise :=
  {| Cyclic.premise_judgment := em_leaf;
     Cyclic.premise_edge := malformed_edge |}.

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

Definition malformed_graph : Cyclic.graph :=
  {| Cyclic.graph_root := em_root;
     Cyclic.graph_nodes :=
       [{| Cyclic.node_judgment := em_root;
           Cyclic.node_payload := Cyclic.RuleNode malformed_rule [1] |};
        {| Cyclic.node_judgment := em_leaf;
           Cyclic.node_payload := Cyclic.AxiomNode em_axiom |}] |}.

Example progress_must_be_valid_is_rejected :
  Cyclic.structural_check malformed_graph = false.
Proof. vm_compute. reflexivity. Qed.

Definition flat_graph : Cyclic.graph :=
  {| Cyclic.graph_root := cycle_companion;
     Cyclic.graph_nodes :=
       [{| Cyclic.node_judgment := cycle_companion;
           Cyclic.node_payload :=
             Cyclic.RuleNode cycle_backlink [1] |};
        {| Cyclic.node_judgment := cycle_companion;
           Cyclic.node_payload :=
             Cyclic.BacklinkNode cycle_backlink 0 |}] |}.

Example flat_graph_is_structurally_well_formed :
  Cyclic.structural_check flat_graph = true.
Proof. vm_compute. reflexivity. Qed.

Example flat_cycle_without_progress_is_rejected :
  Cyclic.relational_check flat_graph = false.
Proof. vm_compute. reflexivity. Qed.
