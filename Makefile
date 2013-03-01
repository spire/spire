all: spire

tmp:
	mkdir tmp

# Let agda figure out the dependencies.
.PHONY: spire
# Compile, putting generated files (except .agdai) in ./tmp.
spire: tmp
	agda -c --compile-dir=tmp -isrc \
	  --ghc-flag="-hidir tmp" --ghc-flag="-odir tmp" --ghc-flag=-isrc \
	  src/spire.agda
	cp tmp/spire ./

clean:
	-rm -rf tmp
	find src -name '*.agdai' -execdir rm {} +
