ROCQ ?= rocq
FLAGS := -Q .. CyclistRocq
CORE := Syntax Substitution Definitions Matching Semantics Rank Rules SourceDefinitions Simplification Input LocalRules Unfolding RuleGeneration Search LazySearch Compiler FastGeneration SealedCompiler
FILES := $(CORE) Adapter Certification Witness CertifiedSearch Benchmarks Examples InputExamples LocalRulesExamples UnfoldingExamples SearchExamples LazySearchExamples CompilerExamples SealedCompilerExamples AdapterExamples WitnessExamples
.PHONY: all core check
all: $(FILES:%=%.vo)
core: $(CORE:%=%.vo)
Syntax.vo: Syntax.v
	$(ROCQ) compile $(FLAGS) $<
Substitution.vo: Substitution.v Syntax.vo
	$(ROCQ) compile $(FLAGS) $<
Definitions.vo: Definitions.v Substitution.vo
	$(ROCQ) compile $(FLAGS) $<
Matching.vo: Matching.v Definitions.vo
	$(ROCQ) compile $(FLAGS) $<
Semantics.vo: Semantics.v Definitions.vo
	$(ROCQ) compile $(FLAGS) $<
Rank.vo: Rank.v Semantics.vo
	$(ROCQ) compile $(FLAGS) $<
Rules.vo: Rules.v Rank.vo Matching.vo
	$(ROCQ) compile $(FLAGS) $<
SourceDefinitions.vo: SourceDefinitions.v Definitions.vo
	$(ROCQ) compile $(FLAGS) $<
Simplification.vo: Simplification.v Rules.vo
	$(ROCQ) compile $(FLAGS) $<
Adapter.vo: Adapter.v Rules.vo
	$(ROCQ) compile $(FLAGS) $<
Certification.vo: Certification.v Adapter.vo
	$(ROCQ) compile $(FLAGS) $<
Input.vo: Input.v Definitions.vo
	$(ROCQ) compile $(FLAGS) $<
InputExamples.vo: InputExamples.v Input.vo SourceDefinitions.vo
	$(ROCQ) compile $(FLAGS) $<
LocalRules.vo: LocalRules.v Simplification.vo
	$(ROCQ) compile $(FLAGS) $<
LocalRulesExamples.vo: LocalRulesExamples.v LocalRules.vo SourceDefinitions.vo
	$(ROCQ) compile $(FLAGS) $<
Unfolding.vo: Unfolding.v Rules.vo
	$(ROCQ) compile $(FLAGS) $<
UnfoldingExamples.vo: UnfoldingExamples.v Unfolding.vo SourceDefinitions.vo
	$(ROCQ) compile $(FLAGS) $<
RuleGeneration.vo: RuleGeneration.v Rules.vo
	$(ROCQ) compile $(FLAGS) $<
Search.vo: Search.v RuleGeneration.vo
	$(ROCQ) compile $(FLAGS) $<
SearchExamples.vo: SearchExamples.v Search.vo
	$(ROCQ) compile $(FLAGS) $<
LazySearch.vo: LazySearch.v Search.vo
	$(ROCQ) compile $(FLAGS) $<
LazySearchExamples.vo: LazySearchExamples.v LazySearch.vo
	$(ROCQ) compile $(FLAGS) $<
Compiler.vo: Compiler.v Search.vo LocalRules.vo Unfolding.vo
	$(ROCQ) compile $(FLAGS) $<
CompilerExamples.vo: CompilerExamples.v Compiler.vo SourceDefinitions.vo
	$(ROCQ) compile $(FLAGS) $<
FastGeneration.vo: FastGeneration.v Compiler.vo
	$(ROCQ) compile $(FLAGS) $<
SealedCompiler.vo: SealedCompiler.v Compiler.vo
	$(ROCQ) compile $(FLAGS) $<
SealedCompilerExamples.vo: SealedCompilerExamples.v SealedCompiler.vo Adapter.vo
	$(ROCQ) compile $(FLAGS) $<
AdapterExamples.vo: AdapterExamples.v Adapter.vo
	$(ROCQ) compile $(FLAGS) $<
Witness.vo: Witness.v Certification.vo
	$(ROCQ) compile $(FLAGS) $<
WitnessExamples.vo: WitnessExamples.v Witness.vo
	$(ROCQ) compile $(FLAGS) $<
CertifiedSearch.vo: CertifiedSearch.v FastGeneration.vo SealedCompiler.vo Witness.vo LazySearch.vo
	$(ROCQ) compile $(FLAGS) $<
Benchmarks.vo: Benchmarks.v Input.vo SourceDefinitions.vo
	$(ROCQ) compile $(FLAGS) $<
Examples.vo: Examples.v Benchmarks.vo CertifiedSearch.vo
	$(ROCQ) compile $(FLAGS) $<
check: all
	$(ROCQ) check $(FLAGS) $(FILES:%=CyclistRocq.FirstOrderNew.%)
