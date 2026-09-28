ROCQCOMPILE := rocq compile
ROCQFLAGS := -Q . CyclistRocq

FILES := \
	Cyclic/Relations.v \
	Cyclic/Framework.v \
	LTL/Syntax.v \
	LTL/Rules.v \
	LTL/Examples.v

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

