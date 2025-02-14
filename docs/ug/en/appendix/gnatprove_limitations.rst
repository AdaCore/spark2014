.. index:: limitations

GNATprove Limitations
=====================

Tool Limitations Leading to an Error Message
--------------------------------------------

.. include:: ../source/unsupported_constructs.rst

Other Tool Limitations
----------------------

.. include:: ../source/other_tool_limitations.rst

Flow Analysis Limitations
-------------------------

These limitations in the flow analysis part of GNATprove may result in a less
precise (but sound) analysis.

.. index:: Depends; limitation

* Flow dependencies caused by record assignments is not captured with perfect
  accuracy. This means that the value of one field might incorrectly be
  considered to participate in the derivation of another field that it does
  not really participate in.

.. index:: initialization; limitation

* Initialization of multi-dimensional arrays with nested FOR loops can be only
  detected if the array bounds are given by static expressions. A possible
  solution is to use :ref:`Aspect Relaxed_Initialization` instead in such a
  case and to prove that only initialized data is read.

Proof Limitations
-----------------

.. include:: ../source/proof_limitations.rst
