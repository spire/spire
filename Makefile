all: spire

tmp:
	mkdir tmp

# Let agda figure out the dependencies.
.PHONY: spire
# Compile, putting generated files (except .agdai) in ./tmp.
spire: tmp
	ghc -isrc -o spire \
	  -hidir tmp -odir tmp \
	  src/Spire.hs

clean:
	-rm -rf tmp
	-rm spire

