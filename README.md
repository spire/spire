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

* [LF in LF: Mechanizing the Metatheory of LF in Twelf - Martens and Crary (2012)]
  (http://www.cs.cmu.edu/~cmartens/lfinlf.pdf)
* [Outrageous but Meaningful Coincidences - McBride (2010)]
  (https://personal.cis.strath.ac.uk/conor.mcbride/pub/DepRep/DepRep.pdf)
* [Type Theory should eat itself - Chapman (2008)]
  (http://cs.ioc.ee/~james/papers/lfmtp08_jmc.pdf)
* [Mechanizing the Metatheory of LF - Urban, Cheney, and Berghofer (2008)]
  (http://arxiv.org/pdf/0804.1667v1.pdf)
* [Mechanizing metatheory in a logical framework - Harper and Licata (2007)]
  (http://www.cs.cmu.edu/~rwh/papers/mech/jfp07.pdf)
* [A Formalisation of a Dependently Typed Language as an Inductive-Recursive Family - Danielsson (2006)]
  (http://www.cse.chalmers.se/~nad/publications/danielsson-types2006.pdf)
* [Coq in Coq - Barras and Werner (1997)]
  (http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.57.4582&rep=rep1&type=pdf)
