Spire
=====

The humble beginnings of a formally verified dependently typed language.

To get an idea of the features the language would ideally support, see
the [roadmap wiki page](https://github.com/spire/spire/wiki/Roadmap).

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

To compile and run:
```
agda -c --compile-dir=. -isrc --ghc-flag=-isrc src/spire.agda
./spire
```

Related Work
------------

There has been a lot of work on formally verifying dependently typed
languages. The goal of Spire is to be an executable programming
environment, making it philosophically different from other work.
Spire extends an [Agda mechanization
of hereditary substitution by Keller and
Altenkirch (2012)](http://www.cs.nott.ac.uk/~txa/publ/msfp10.pdf) to a
dependent type system, making it also technically different.
The wiki contains a
[list of related projects](https://github.com/spire/spire/wiki/Related-Work).
