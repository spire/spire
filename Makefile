all: spire

tmp:
	mkdir tmp

.PHONY: spire
# Compile, putting generated files in ./tmp.
spire: tmp
	ghc -O2 -isrc -o spire \
	  -hidir tmp -odir tmp \
	  src/Spire.hs

clean:
	-rm -rf tmp
	-rm spire

