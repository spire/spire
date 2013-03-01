# Let agda figure out the dependencies.
.PHONY: spire
spire:
	agda -c --compile-dir=. -isrc --ghc-flag=-isrc src/spire.agda
