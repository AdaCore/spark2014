.. _shared_variable_control:

Shared Variable Control (Annex C.6)
===================================

The following restrictions are applied to the declaration of volatile types
and objects in |SPARK|:

.. centered:: **Legality Rules**

#. A volatile representation aspect may only be applied to an 
   ``object_declaration`` or a ``full_type_declaration``.
   
#. A component of an ``array_type_declaration`` or a ``record_type_declaration`` 
   shall not be of a volatile type. [This may require determining whether a
   private type is volatile.]
   
#. A discriminant shall not be of a volatile type.

#. Neither a discriminated type nor an object of such a type shall be volatile.

#. Neither a tagged type nor an object of such a type shall be volatile.
   

