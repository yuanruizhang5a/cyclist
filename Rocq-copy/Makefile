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
	SP/Search.v

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
