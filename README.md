Spire
=====

A dependently typed language that makes generic programming easy. Read the
["leveling up" paper](https://github.com/larrytheliquid/leveling-up)
to get an idea of what the  final language will support, in terms of
generic programming.

Future Work
-----------

The current implementation is written in Haskell. The semantics is defined
using hereditary substitution. Hereditary substitution has its
roots in making a PL's semantics syntactically terminating. We hope
to use this Haskell implementation as a prototype, and ultimately end
up with a formally mechanized implementation in Agda that capitalizes
on the termination properties of hereditary substitution.
