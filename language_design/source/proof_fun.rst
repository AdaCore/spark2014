Proof functions
===============

A function which has the following aspect::

   Convention => SPARK_Proof

is declared as being a proof function. As a consequence, no body can be given
for this subprogram. Other aspects such as ``Param_In``, ``Global_In``, ``Pre``
and ``Post`` are allowed.

Legality rules
--------------

Proof functions are not allowed to write any global variables, so the Aspects
``Global_In_Out``, ``Global_Out`` and their equivalent for parameters, as well
as the ``Derives`` aspect, are not allowed.

Proof semantics
---------------

Proof functions can be called only in annotations such as ``Pre`` and ``Post``
and pragma ``Assert``. They have the same semantics as a call to a regular
function, that is, only the information contained in the contract is known at
the point of call.

Dynamic semantics
-----------------

It is not clear yet what the dynamic semantics of proof functions will be.
