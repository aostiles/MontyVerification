.PHONY: build examples clean

# Build the codegen binary.
build:
	lake build

# Run the worked examples end-to-end.
examples: build
	python3 examples/run_examples.py -j 8

clean:
	lake clean
