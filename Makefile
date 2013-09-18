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

######################################################################
# The unification code is in a separate repo.

lib/unify.git:
	git clone git@github.com:spire/type-inference.git lib/unify.git

lib-unify-deps: lib/unify.git
	make -C lib/unify.git deps

lib-unify: lib/unify.git
	make -C lib/unify.git
