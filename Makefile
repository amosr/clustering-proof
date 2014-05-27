
# -- Config ---------------------------------------------------------
# Coq binaries to use when building
COQDEP		= coqdep
COQC		= coqc
THREADS		= 16


# -- Roots ----------------------------------------------------------
#  I have no idea why this works, but $(src_coq_vo) doesn't.
root = $(patsubst %.v,%.vo,$(shell find Clustering -iname "*.v"))

# -------------------------------------------------------------------
.PHONY : all
all:
	@$(MAKE) deps
	@$(MAKE) proof -j $(THREADS)


# Build the Coq proofs.
.PHONY: proof
proof: $(root)


# Start the Coq ide
.PHONY: start
start: 
	coqide -R Clustering -as Clustering &

# Build dependencies for Coq proof scripts.
.PHONY: deps
deps: make/proof.deps

# Find Coq proof scripts
src_coq_v \
 = 	$(shell find Clustering  -name "*.v" -follow) \

# Coqc makes a .vo and a .glob from each .v file.
src_coq_vo	= $(patsubst %.v,%.vo,$(src_coq_v))
	
make/proof.deps : $(src_coq_v)
	@echo "* Building proof dependencies"
	@$(COQDEP) -R Clustering -as Clustering $(src_coq_v) > make/proof.deps
	@cp make/proof.deps make/proof.deps.inc


# Clean up generated files.
.PHONY: clean
clean : 
	@rm -f make/proof.deps
	@rm -f make/proof.deps.inc

	@find .    -name "*.vo" \
		-o -name "*.glob" \
		-follow | xargs -n 1 rm -f

# Rules 
%.vo %.glob : %.v
	@echo "* Checking $<"
	@$(COQC) -R Clustering Clustering $<


# Include the dependencies.
-include make/proof.deps.inc

