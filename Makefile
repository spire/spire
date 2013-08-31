all: spire

.PHONY: deps
deps:
	cabal install wl-pprint parsec mtl syb hunit

tmp:
	mkdir tmp

.PHONY: spire
# Compile, putting generated files in ./tmp.
#
# The -fno-warn-unused-binds turns off warns about unused and
# unexported top-level defs, and unused local defs, but not unused
# pattern bindings.  Those can be disabled with
# -fno-warn-unused-matches.
spire: tmp
	ghc -W -fno-warn-unused-binds \
    -isrc -o spire \
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

