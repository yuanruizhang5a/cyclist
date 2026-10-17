.PHONY: all common benchmarks fopl ppl check
all: benchmarks
common:
	python3 -B build.py --common
benchmarks:
	python3 -B run_benchmarks.py --suite all
fopl:
	python3 -B run_benchmarks.py --suite fopl
ppl:
	python3 -B run_benchmarks.py --suite ppl
check: benchmarks
	python3 -B check_integrity.py --kernel
