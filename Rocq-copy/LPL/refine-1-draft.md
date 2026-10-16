Make a plan that refine this current code Rocq-copy/LPL. A copy of Rocq-copy/LPL is saved as in Rocq-copy/LPL-old. 

## Requirements

Based on the current implementation of G3FOPL in Rocq-copy/LPL-old, enrich Rocq-copy/LPL with the theory of G3PPL; Make G3PPL a general theory and make the current G3FOPL a special theory of G3PPL; Also propose some benchmarks for G3PPL and test them. 

- Following the implementation of G3FOPL, implement the theory of G3PPL in Rocq in Rocq-copy/LPL. Make atom programs, atom formulas, relations between label variables for worlds of G3PPL (and other related structures if there are) parameters in Rocq that can be instantiated into any DIY structures. 
  
- As in IMPLEMENTATION_PLAN.md, realizing the syntax, semantics, rules and rule generations for G3PPL. 

- After realizing G3FOPL, make the current theory of G3FOPL an instance of G3PPL, by instantiating the atom programs and formulas, relations between label variables for worlds as the corresponding structures defined in Rocq-copy/LPL-old. Note that do NOT alter the content of the current theory of G3FOPL, but only re-write them in suitable forms and put all the modified .v files for G3FOPL in a sub-folder ``FOPL/``. 
    
    According to the theory in the folder ``Theory``, new implementation of G3FOPL should only expand the structures of G3PPL (in its own Syntax.v file); add special rules to those of G3PPL (in its own Rules.v file) (now, most rules in G3FOPL in Rocq-copy/LPL-old should become general rules of G3PPL).  

- Should faithfully follow the theory as described in ``Theory``. The same as in IMPLEMENTATION_PLAN.md, when meeting problems, show your recommendation, but let the user decide. 

- After realizing G3PPL and finishing modifying G3FOPL, re-test the same benchmark for G3FOPL. Then following the same principles of IMPLEMENTATION_PLAN.md to generate benchmarks for G3PPL, and test them. For each benchmark, do not exceed the max 10 minutes as in IMPLEMENTATION_PLAN.md.  

Other general requirements:
- Keep all files not in Rocq-copy/LPL unchanged. 
- After create the plan, write it into a .md file.  