ROCQCOMPILE := rocq compile
ROCQFLAGS := -Q . CyclistRocq

FILES := \
	Cyclic/Relations.v \
	Cyclic/Framework.v \
	LTL/Syntax.v \
	LTL/Rules.v \
	LTL/Examples.v \
	FirstOrder/Syntax.v \
	FirstOrder/Semantics.v \
	FirstOrder/Rules.v \
	FirstOrder/Automation.v \
	FirstOrder/Certification.v \
	FirstOrder/RuleGeneration.v \
	FirstOrder/GraphSearch.v \
	FirstOrder/Definitions.v \
	FirstOrder/Derived.v \
	FirstOrder/Benchmarks.v \
	FirstOrder/Search.v \
	SP/Syntax.v \
	SP/Semantics.v \
	SP/Rules.v \
	SP/Automation.v \
	SP/Certification.v \
	SP/RuleGeneration.v \
	SP/GraphSearch.v \
	SP/Definitions.v \
	SP/Benchmarks.v \
	SP/Examples.v \
	SP/Tests.v \
	SP/Search.v \
	LPL/Signature.v \
	LPL/Syntax.v \
	LPL/Semantics.v \
	LPL/Progress.v \
	LPL/Rules.v \
	LPL/RuleGeneration.v \
	LPL/Certification.v \
	LPL/Benchmarks/Support.v \
	LPL/Benchmarks/InvariantSupport.v \
	LPL/Benchmarks/Labels.v \
	LPL/Benchmarks/Signatures.v \
	LPL/Benchmarks/Updates.v \
	LPL/Benchmarks/Tests.v \
	LPL/Benchmarks/RegularPrograms.v \
	LPL/Benchmarks/Booleans.v \
	LPL/Benchmarks/Quantifiers.v \
	LPL/Benchmarks/Temporal.v \
	LPL/Benchmarks/AssignmentChange.v \
	LPL/Benchmarks/RuleCoverage.v \
	LPL/Benchmarks/CheckerNegative.v \
	LPL/Benchmarks/Cyclic.v \
	LPL/Benchmarks/CyclicTags.v \
	LPL/Benchmarks/CounterLoop.v \
	LPL/Benchmarks/NestedProgram.v

VOS := $(FILES:.v=.vo)

.PHONY: all
all: $(VOS)

Cyclic/Relations.vo: Cyclic/Relations.v
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

Cyclic/Framework.vo: Cyclic/Framework.v Cyclic/Relations.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

LTL/Syntax.vo: LTL/Syntax.v Cyclic/Framework.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

LTL/Rules.vo: LTL/Rules.v LTL/Syntax.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

LTL/Examples.vo: LTL/Examples.v LTL/Rules.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

FirstOrder/Syntax.vo: FirstOrder/Syntax.v Cyclic/Framework.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

FirstOrder/Semantics.vo: FirstOrder/Semantics.v FirstOrder/Syntax.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

FirstOrder/Rules.vo: FirstOrder/Rules.v FirstOrder/Semantics.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

FirstOrder/Automation.vo: FirstOrder/Automation.v FirstOrder/Semantics.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

FirstOrder/Certification.vo: FirstOrder/Certification.v FirstOrder/Rules.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

FirstOrder/RuleGeneration.vo: FirstOrder/RuleGeneration.v FirstOrder/Rules.vo FirstOrder/Automation.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

FirstOrder/GraphSearch.vo: FirstOrder/GraphSearch.v FirstOrder/RuleGeneration.vo FirstOrder/Certification.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

FirstOrder/Definitions.vo: FirstOrder/Definitions.v FirstOrder/Syntax.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

FirstOrder/Derived.vo: FirstOrder/Derived.v FirstOrder/Semantics.vo FirstOrder/Definitions.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

FirstOrder/Benchmarks.vo: FirstOrder/Benchmarks.v FirstOrder/Rules.vo FirstOrder/Derived.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

FirstOrder/Search.vo: FirstOrder/Search.v FirstOrder/Benchmarks.vo FirstOrder/GraphSearch.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

SP/Syntax.vo: SP/Syntax.v Cyclic/Framework.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

SP/Semantics.vo: SP/Semantics.v SP/Syntax.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

SP/Rules.vo: SP/Rules.v SP/Semantics.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

SP/Automation.vo: SP/Automation.v SP/Semantics.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

SP/Certification.vo: SP/Certification.v SP/Rules.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

SP/RuleGeneration.vo: SP/RuleGeneration.v SP/Rules.vo SP/Automation.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

SP/GraphSearch.vo: SP/GraphSearch.v SP/RuleGeneration.vo SP/Certification.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

SP/Definitions.vo: SP/Definitions.v SP/Syntax.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

SP/Benchmarks.vo: SP/Benchmarks.v SP/Definitions.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

SP/Examples.vo: SP/Examples.v SP/GraphSearch.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

SP/Tests.vo: SP/Tests.v SP/RuleGeneration.vo SP/Benchmarks.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

SP/Search.vo: SP/Search.v SP/GraphSearch.vo SP/Benchmarks.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

# LPL has no proof-search dependency. Benchmarks are independently limited.
LPL_COMMON := LPL/Signature.v LPL/Syntax.v LPL/Semantics.v LPL/Progress.v LPL/Rules.v LPL/RuleGeneration.v LPL/Certification.v LPL/Benchmarks/Support.v LPL/Benchmarks/InvariantSupport.v
LPL_BENCHMARKS := LPL/Benchmarks/Labels.v LPL/Benchmarks/Signatures.v LPL/Benchmarks/Updates.v LPL/Benchmarks/Tests.v LPL/Benchmarks/RegularPrograms.v LPL/Benchmarks/Booleans.v LPL/Benchmarks/Quantifiers.v LPL/Benchmarks/Temporal.v LPL/Benchmarks/AssignmentChange.v LPL/Benchmarks/RuleCoverage.v LPL/Benchmarks/CheckerNegative.v LPL/Benchmarks/Cyclic.v LPL/Benchmarks/CyclicTags.v LPL/Benchmarks/CounterLoop.v LPL/Benchmarks/NestedProgram.v
.PHONY: lpl lpl-common lpl-benchmarks
lpl-common: $(LPL_COMMON:.v=.vo)
lpl: lpl-common $(LPL_BENCHMARKS:.v=.vo)
lpl-benchmarks: lpl-common
	python3 LPL/run_benchmarks.py

LPL/Signature.vo: LPL/Signature.v
	$(ROCQCOMPILE) $(ROCQFLAGS) $<
LPL/Syntax.vo: LPL/Syntax.v LPL/Signature.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<
LPL/Semantics.vo: LPL/Semantics.v LPL/Syntax.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<
LPL/Progress.vo: LPL/Progress.v LPL/Semantics.vo Cyclic/Framework.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<
LPL/Rules.vo: LPL/Rules.v LPL/Progress.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<
LPL/RuleGeneration.vo: LPL/RuleGeneration.v LPL/Rules.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<
LPL/Certification.vo: LPL/Certification.v LPL/Rules.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<
LPL/Benchmarks/Support.vo: LPL/Benchmarks/Support.v LPL/RuleGeneration.vo LPL/Certification.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<
LPL/Benchmarks/InvariantSupport.vo: LPL/Benchmarks/InvariantSupport.v
	$(ROCQCOMPILE) $(ROCQFLAGS) $<
LPL/Benchmarks/CyclicTags.vo: LPL/Benchmarks/Cyclic.vo
LPL/Benchmarks/%.vo: LPL/Benchmarks/%.v LPL/Benchmarks/Support.vo LPL/Benchmarks/InvariantSupport.vo
	timeout --signal=KILL 600s $(ROCQCOMPILE) $(ROCQFLAGS) $<
