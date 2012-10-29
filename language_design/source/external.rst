Modeling of external state
==========================

One can model some piece of external state, which can or will change
independently of the internal state of the program::

    V : T with Volatile => True;

Proof semantics
---------------

A volatile variable is assumed to potentially change after each read.

Dynamic semantics
-----------------

This pragma does not have dynamic semantics.
