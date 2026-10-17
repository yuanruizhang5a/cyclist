Make a plan that refines this current code Rocq-copy/LPL.  

## Requirements

The current theory of G3PPL has several problems:

1. The `Atom` in `formula` should be more general, in the sense that we should NOT assume it has `args` (of course we can still add additional args in G3FODL). It should be a pure carrier, can be any DIY structure. 
   - The same for `Atomic`, we should NOT assume that it has a `value`. 
   - And `formula` should NOT contain a `BinaryAtom`. If want to express binary relations in special theories, they should be defined as a special `Atom`. 
   - Check this and revise if needed: The rules at the level of G3PPL, as in the manuscript of `Theory`, should be independent from these parameters. And do NOT include special rules that rely on these parameters. Special rules should be added in special theories based on G3PPL. The same as other parts, like `rule generations`, `certifications`, etc. And on the other hand, the special theories (like in the sub-folders `PPL` and `FOPL`) should NEVER re-invent similar rules at the level of G3PPL, but apply them (under special parameters). 
2. `formula` should ONLY contain primitive operators: `Truth`, `Neg`, `Conj`, `Extension`, `First`, `Suffix`, `Box`. Other operators are still needed, but they should be defined based on these primitive operators outside `formula`. 

Consider if the above problems can be dealt with, make a plan if possible, or interact with the user if needed. 

## Other General Requirements

Modify existing benchmarks accordingly and re-run them. But do NOT add new benchmarks. 

After revising, check the integrity of the whole code, remove redundant code, and ensure all changes are consistent with the revised theory. 

In the plan, put ``Put this plan into a .md file before implementing it``. 