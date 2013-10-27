.. _shared_variable_control:

Shared Variable Control (Annex C.6)
===================================

The following restrictions are applied to the declaration of volatile types
and objects in |SPARK|:

.. centered:: **Legality Rules**

.. _tu-shared_variable_control-01:

1. A volatile representation aspect may only be applied to an 
   ``object_declaration`` or a ``full_type_declaration``.
   
.. _tu-shared_variable_control-02:

2. A component of a non-volatile type declaration shall not be volatile.

.. todo:: This may require determining whether a private type is volatile.

.. todo:: The above two rules may be relaxed in a future version.
   
.. _tu-shared_variable_control-03:

3. A discriminant shall not be of a volatile type.

.. _tu-shared_variable_control-04:

4. Neither a discriminated type nor an object of such a type shall be volatile.

.. _tu-shared_variable_control-05:

5. Neither a tagged type nor an object of such a type shall be volatile.

.. _tu-shared_variable_control-06:

6. A volatile variable shall only be declared at library-level.
   
.. _etu-shared_variable_control:


