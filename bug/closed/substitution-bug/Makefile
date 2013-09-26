ROOT = $(shell git rev-parse --show-toplevel)

all:
	ghc -i$(ROOT)/src -outputdir /tmp -o /tmp/a.out SubstitutionBug.hs
	/tmp/a.out
	$(ROOT)/spire SubstitutionBug.spire