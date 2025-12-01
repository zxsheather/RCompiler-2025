.PHONY: build run

build:
	cargo build

run:
	@./target/debug/RCompiler-2025 --emit-ir
