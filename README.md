Spire
=====

A dependently typed language that makes generic programming easy. Read the
["leveling up" paper](https://github.com/larrytheliquid/leveling-up)
to get an idea of what the final language will support, in terms of
generic programming support.

The current implementation is written in Haskell. The semantics is defined
using hereditary substitution. Hereditary substitution has its
roots in making a PL's semantics syntactically terminating. We hope
to use this Haskell implementation as a prototype, and ultimately end
up with a formally mechanized implementation in Agda that capitalizes
on the termination properties of hereditary substitution.

Related Work
------------

There has been a lot of work on formally verifying dependently typed
languages. The wiki contains a
[list of related
projects](https://github.com/spire/spire/wiki/Related-Work), and you
are welcome to add to this list.

The goal of Spire is to be an executable programming
environment, making it philosophically different from other work.
Spire extends an [Agda mechanization
of hereditary substitution by Keller and
Altenkirch (2010)](http://hal.inria.fr/docs/00/52/06/06/PDF/msfp10.pdf) to a
dependent type system, making it also technically different.
