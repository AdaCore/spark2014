Representation Issues
=====================

Representation Clauses
----------------------

Representation clauses are in |SPARK|, except for ``'Address`` representation
clauses.

As aspects specifications are elaborated at the freezing point of the
associated entity, this allows forward references in the expression associated
to the aspect specification, as in:

.. code-block:: ada

   procedure Incr (X : in out Integer) with
     Post => X = Add_One (X'Old);

   function Add_One (X : Integer) return Integer is (X + 1);

No such forward references are allowed in |SPARK|.

Machine Code Insertions
-----------------------

Machine code insertions are not in |SPARK|.

Unchecked Type Conversions
--------------------------

Unchecked type conversions are not in |SPARK|.

Streams
-------

Stream ``Read`` and ``Write`` operations are not in |SPARK|.

Interfacing to Other Languages
------------------------------

Pragma or aspect ``Unchecked_Union`` is not in |SPARK|.
