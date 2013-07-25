all: spire

.PHONY: deps
deps:
	cabal install wl-pprint parsec mtl syb hunit

tmp:
	mkdir tmp

.PHONY: spire
# Compile, putting generated files in ./tmp.
spire: tmp
	ghc -isrc -o spire \
	  -hidir tmp -odir tmp \
	  src/Spire.hs

clean:
	-rm -rf tmp
	-rm spire

test:
	runghc -isrc src/Spire/Test.hs examples

ott: ott
	ott -i formalization/ott/spire.ott -o formalization/ott/spire.tex
	pdflatex -output-directory formalization/ott/ formalization/ott/spire.tex

