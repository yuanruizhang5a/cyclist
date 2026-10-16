
Make a plan for implementing the theory of Labelled Process Logic (LPL) in Rocq. 

## Requirements

Read the manuscripts in Rocq-copy/LPL/Theory and the code repo. in current path, especially Rocq-copy/Cyclic, Rocq-copy/LTL, Rocq-copy/FirstOrder. Make a plan to implement the theory of LPL in Rocq, following the following requirements:

  - The theory must base on the cyclic framework implemented in Rocq-copy/Cyclic (Rocq-copy/Cyclic must be kept unchanged). 
  - Adopt a similar shallow embedding way as in Rocq-copy/FirstOrder and Rocq-copy/LTL to implement the syntax and semantics of LPL: Two layers of implementations in Rocq: Judgements are used for cyclic deductions in cyclic graphs, while judgements' meaning are denoted by actual Propositions in Rocq. Define the syntax and semantics in separated files. 
  - Use similar ``rule_instance`` structures as in Rocq-copy/FirstOrder to implement each rule.  
  - Implement rule generations for the rule_instances in LPL similarly to what it is done in FirstOrder/RuleGeneration.v. 
  - Currently, only focus on the first-order LPL (i.e., G3FOPL). The FOL theory of FOPL must be able to handle any given signatures. Refer to Rocq-copy/FirstOrder to define a similar one. But unlike Rocq-copy/FirstOrder, should be able to handle all logic connectives: and, or, implication, and negation just as in the manuscript. Different from FirstOrder, each predicate does not have to be defined based on induction (and it does not matter because we do not need to prove the pure FOL formulas in LPL, which is not like in FirstOrder). 
  - Currently, do not need to implement proof search tactics. All proofs are manually handled in benchmarks. 
  - Currently, do NOT handle pure FOL formulas. In benchmarks, try only default tactics in Rocq to handle pure FOL formulas: do NOT try link the theory of Rocq-copy/FirstOrder or use extra libs not in Rocq's library. If cannot solve, modify or give up that benchmark. 
  - Since we are not going to derive pure FOL formulas, introduce the forall and exists quantifiers, do NOT make simplifications as in Rocq-copy/FirstOrder (where it only defines free and existential variables without introducing forall and exists operators). 
  - After the code generation, generate several benchmarks to test the code. The benchmarks should cover various cases of LPL formulas and rules. Should contain both simple and complex examples of programs and formulas. 
  - When testing benchmarks, 10 minutes is the max time allowed for each benchmark. If exceeding it, modify or abandon it by creating a simpler benchmark. 


## Other general requirements:
- Try to faithfully follow the theory in Rocq-copy/LPL/Theory. But if found something wrong, try to make a compatible version in Rocq with Rocq-copy/FirstOrder. If not sure, do not guess, always interact with the user and let the user decide. 
- Currently, do NOT implement any automation procedures as in the code repo of current path. Only realize the syntax, semantics, the proof rules of LPL, as well as the ``rule generation'' part that for generating rule_instances as in Rocq-copy/FirstOrder/RuleGeneration.v. If any places not clear, ask the user. 
- Do NOT need to deal with the completeness fo the theory. The soundness of the theory should follow Rocq-copy/FirstOrder (since it is a general framework). 
- Do NOT read Rocq-copy/FirstOrderNew as a reference. 
- Write this plan into a .md file before implementing it. 