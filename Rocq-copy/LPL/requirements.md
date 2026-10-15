## Requirements When Generating Code

1. Do not assume special FO domain. ()
2. Have to consider logic connectives: and, or, implication, and negation just as in the manuscript. 
3. For sequent that contains only pure FOL formulas, firstly try to prove using the default tactics in Rocq; If not, try to convert to formulas that can be solved by SMTCoq, and call SMTCoq; If still not work, stall the proof process and leave it to the reader. 
4. For sequent rules, should use similar ``rule_instance`` structure as in FirstOrder. 
5. Since we are not going to derive pure FOL formulas, introduce the forall and exists quantifiers, do not make simplification as in FirstOrder. (But need to analyze which types of FOL formulas can be dealt with by Rocq itself or SMTCoq, and which types should be left to the solver. )