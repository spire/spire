Spire
=====

A dependently typed language that makes generic programming easy. Read the
["leveling up" paper](https://github.com/larrytheliquid/leveling-up)
to get an idea of what the  final language will support, in terms of
generic programming.

Type checking
-------------

To build the Spire language binary, type `make` in the root directory of this project.

Now you can pass the location of file to be type checked:

```
./spire examples/Basic.spire
```

### Development

When developing, it can be tedious to recompile the executable all the time. You can run Spire with runghc instead:

```
cd src
runghc Spire.hs ../examples/Basic.spire 
````

Emacs mode
----------

### Configuration

There is an Emacs mode for Spire, which can be found in `editors/emacs/spire-model`.

Add the following to your Emacs initialization file:

```
(load-file "/PATH-TO-SPIRE-CHECKOUT/src/spire/editor/emacs/spire-mode.el")
(require 'spire-mode)
```

Now customize the Emacs variable that specifies the location of the Spire executable:

```
M-x customize group
spire
```

Then set the `Spire Command` variable to the location of the executable:

1. Fill in `Spire Command` with `/PATH-TO-SPIRE-CHECKOUT/spire`.
2. Click `Save for future sessions`.
3. Click `Exit`.

### Using the mode

Syntax highlighting will automatically be performed for any files with a `.spire` suffix.

To type check the current file:

```
C-C C-l
```

The results of type checking appear in a separate Emacs window.

End goal
--------

The current implementation is written in Haskell. The semantics is defined
using hereditary substitution. Hereditary substitution has its
roots in making a PL's semantics syntactically terminating. We hope
to use this Haskell implementation as a prototype, and ultimately end
up with a formally mechanized implementation in Agda that capitalizes
on the termination properties of hereditary substitution.
