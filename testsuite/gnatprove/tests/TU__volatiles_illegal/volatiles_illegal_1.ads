with System.Storage_Elements;

package Volatiles_Illegal_1
  with SPARK_Mode,
       Abstract_State => ((State1 with External => (Async_Readers,
                                                    Async_Writers => True)),
       --  TU: 2. If just the name of the property is given then its value
       --  defaults to True [; for instance Async_Readers defaults to
       --  Async_Readers => True].

       --  TU: 4. If any one property is explicitly defined, all undefined
       --  properties default to a value of False.

                          (State2 with External => Async_Readers),
       --  TU: 3. An External state abstraction shall have each of the
       --  properties set to True which are True for any of its
       --  ``constituents``.

                          State3,
       --  TU: 1. A state abstraction that is not specified as External shall
       --  not have ``constituents`` which are External states.

       --  TU: 8. An External state abstraction is one declared with an
       --  ``option_list`` that includes the External ``option``
       --  (see :ref:`external_state`).

                          (State4 with External))
       --  TU: 2. An External state abstraction shall have at least one
       --  ``constituent`` that is External state, or shall have a null
       --  refinement.
is
   A : Integer;

   Vol : Integer
     with Volatile,
          Async_Readers,
          Async_Writers,
          Effective_Reads,
          Address => System.Storage_Elements.To_Address (16#A11#);

   pragma Elaborate_Body (Volatiles_Illegal_1);
end Volatiles_Illegal_1;
