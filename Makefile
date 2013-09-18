all: spire

# This must be run manually whenever the deps change.
deps: lib-unify-deps lib-unify
	cabal install wl-pprint parsec mtl syb hunit unbound

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
	ghc \
	  -W -fno-warn-unused-binds \
	  -isrc \
	  -outputdir tmp \
	  -o spire \
	  src/Spire.hs

clean:
	-rm -rf tmp
	-rm spire

test:
	runghc -isrc src/Spire/Test.hs examples

ott: ott
	ott -i formalization/ott/spire.ott -o formalization/ott/spire.tex
	pdflatex -output-directory formalization/ott/ formalization/ott/spire.tex

tags: tmp
	cd tmp \
	&& find ../src -name '*.hs' -print \
	   | xargs hasktags --etags

######################################################################
# The unification code is in a separate repo.

lib/unify.git:
	git clone git@github.com:spire/type-inference.git lib/unify.git

lib-unify-deps: lib/unify.git
	make -C lib/unify.git deps

lib-unify: lib/unify.git
	make -C lib/unify.git
