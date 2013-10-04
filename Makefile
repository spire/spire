all: spire

# This must be run manually whenever the deps change.
#
# Try 'make -i deps' if make gives you trouble ...
deps: lib-unify-deps lib/unify.git
	cabal install wl-pprint parsec mtl syb hunit unbound cmdargs

.PHONY: spire
# Compile, putting generated files in ./tmp.
#
# The -fno-warn-unused-binds turns off warns about unused and
# unexported top-level defs, and unused local defs, but not unused
# pattern bindings.  Those can be disabled with
# -fno-warn-unused-matches.
spire: tmp lib-unify
	ghc \
	  -W -fno-warn-unused-binds \
	  -isrc \
	  -outputdir tmp \
	  -o spire \
	  $(GHC_PROF) \
	  src/Spire.hs

# Build spire with profiling enabled, so that e.g. we can see stack
# traces on exceptions with
#
#   ./spire +RTS -xc -RTS <input file>
#
# To generate debug objects we use the special "man in a monocle"
# object suffix.
#
# The multi-line make target sets make variables locally:
# https://www.gnu.org/software/make/manual/make.html#Target_002dspecific
#
# To reinstall your cabal libs with profiling see
# http://stackoverflow.com/questions/1704421/cabal-not-installing-dependencies-when-needing-profiling-libraries
# (the "--reinstall world" part did not work for me, but after hiding
# the *local* package database with
# `mv ~/.ghc/<ghc-version>/package.conf.d{,.hidden}`
# I successfully reinstalled the deps with `make deps`).
debug: GHC_PROF += -prof -fprof-auto -osuf p_o -outputdir tmp/prof
debug: UNIFY_TARGET = cabal-install-debug
debug: spire

######################################################################

clean:
	-rm -rf tmp
	-rm spire

test: lib-unify
	runghc -isrc src/Spire/Test.hs examples

ott: ott
	ott -i formalization/ott/spire.ott -o formalization/ott/spire.tex
	pdflatex -output-directory formalization/ott/ formalization/ott/spire.tex

# It seems that hasktags is broken for literate haskell!  Weird,
# because it tries to support it, and does find the defs, but just
# fails to include the leading '> ' in the output TAGS file???  So, we
# add back the leading ">".
#
# More hasktags bugs:
#
# - the --append option results in no tags! (Note that our use of
#   xargs is not completely safe, but the output of
#
#     xargs --show-limits < /dev/null
#
#   indicates we don't have much to worry about).
#
# - does not find 'data' defs when the "=" is on the next line.
#
# - sometimes M-. brings me to a use and not the def, e.g. for
#   'Entry'.
tags: tmp
	-rm tmp/TAGS
	cd tmp \
	&& find ../lib/unify.git/src/PatternUnify \
	        ../lib/unify.git/src/Common \
	        -name '*.lhs' -print \
	   | xargs hasktags --etags \
	&& sed -i -re 's/^( +)/>\1/' TAGS \
	&& mv TAGS TAGS1
	cd tmp \
	&& find ../src -name '*.hs' -print \
	   | xargs hasktags --etags \
	&& mv TAGS TAGS2 && cat TAGS* > TAGS

tmp:
	mkdir tmp

######################################################################
# The unification code is in a separate repo.

lib/unify.git:
	git clone git@github.com:spire/type-inference.git lib/unify.git

lib-unify-deps: lib/unify.git
	make -C lib/unify.git deps

lib-unify: lib/unify.git
	make -C lib/unify.git $(UNIFY_TARGET)
