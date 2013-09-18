all: spire

deps: lib-unify-deps
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
#
# The -package-conf <conf> makes the unification code available to GHC
# as a package without having to install the package.  When GHC is run
# in --make mode (the default), where it does automatic dependency
# calculation, it requires all modules to be given in source form or
# in packages; giving the path to a the .o or .hi files does not work
# :P
spire: tmp lib-unify
	ghc \
	  -W -fno-warn-unused-binds \
	  -package-conf lib/unify.git/src/dist/package.conf.inplace \
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
