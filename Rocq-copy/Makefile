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
	FirstOrder/Definitions.v \
	FirstOrder/Derived.v \
	FirstOrder/Benchmarks.v \
	FirstOrder/Search.v

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

FirstOrder/Definitions.vo: FirstOrder/Definitions.v FirstOrder/Syntax.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

FirstOrder/Derived.vo: FirstOrder/Derived.v FirstOrder/Semantics.vo FirstOrder/Definitions.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

FirstOrder/Benchmarks.vo: FirstOrder/Benchmarks.v FirstOrder/Rules.vo FirstOrder/Derived.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<

FirstOrder/Search.vo: FirstOrder/Search.v FirstOrder/Benchmarks.vo
	$(ROCQCOMPILE) $(ROCQFLAGS) $<
