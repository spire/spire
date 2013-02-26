Spire
=====

The humble beginnings of a formally verified dependently typed language.

Current Status
--------------

Spire is currently a trivial simply typed language. The implementation
is formally mechanized in Agda. The semantics of the language is
defined using hereditary substitution based on the
[Agda mechanization by Keller and Altenkirch](http://www.cs.nott.ac.uk/~txa/publ/msfp10.pdf).

Work In Progress
----------------

Extending the hereditary substitution mechanization to define a very
basic dependently typed language.

Running
-------

Spire uses Agda's Haskell backend for compilation.
Haskell and Agda communicate via Agda's FFI.
The CLI and parser are informally written in Haskell.
Everything else is formally mechanized in Agda.

To compile:
```
agda -c --compile-dir=. -isrc --ghc-flag=-isrc src/spire.agda
```

To run:
```
./spire
```
