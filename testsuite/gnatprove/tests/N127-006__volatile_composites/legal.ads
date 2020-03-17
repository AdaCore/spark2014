package Legal
  with SPARK_Mode => On
is
   --  Tests for volatile variable usages, where the usage should
   --  be legal in SPARK 14.0.2+

   --  In particular, this test illustrates the reading and writing
   --  of volatile composite objects, which are introduced in SPARK 14.0.2+
   --  as a result of adding the fifth bullet below to RM rule 7.1.3(10)

   --  TU: 12. Contrary to the general |SPARK| rule that expression evaluation
   --  cannot have side effects, a read of an effectively volatile object with
   --  the properties Async_Writers or Effective_Reads set to True is
   --  considered to have an effect when read. To reconcile this
   --  discrepancy, a name denoting such an object shall only occur in
   --  a *non-interfering context*. A name occurs in a non-interfering
   --  context if it is:
   --
   --  * the name on the left-hand side of an assignment statement; or
   --
   --  * the [right-hand side] expression of an assignment statement; or
   --
   --  * the expression of an initialization expression of an object
   --    declaration; or
   --
   --  * the ``object_name`` of an ``object_renaming_declaration``; or
   --
   --  * the actual parameter in a call to an instance of Unchecked_Conversion
   --    whose result is renamed [in an object renaming declaration]; or
   --
   --  * an actual parameter in a call for which the corresponding
   --    formal parameter is of a non-scalar effectively volatile type; or
   --  * the (protected) prefix of a name denoting a protected operation; or
   --
   --  * the return expression of a ``simple_return_statement`` which applies
   --    to a volatile function; or
   --
   --  * the initial value expression of the
   --    ``extended_return_object_declaration`` of an
   --   ``extended_return_statement`` which applies to a volatile function; or
   --
   --  * the prefix of a ``slice``, ``selected_component``,
   --    ``indexed_component``, or ``attribute_reference`` which is itself a
   --    name occurring in a non-interfering context; or
   --
   --  * the prefix of an ``attribute_reference`` whose
   --    ``attribute_designator`` is either Address, Alignment, Component_Size,
   --    First_Bit, Last_Bit, Position, Size, or Storage_Size; or
   --
   --  * the expression of a type conversion occurring in a non-interfering
   --    context.
   --
   --  [The attributes listed above all have the property that when their
   --  prefix denotes an object, evaluation of the attribute involves
   --  evaluation of only the name, not the value, of the object.]
   --
   --  The same restrictions also apply to a call to a volatile function
   --  (except not in the case of an internal call to a protected function
   --  which is nonvolatile for internal calls) and to the evaluation of any
   --  attribute which is defined to introduce an implicit dependency on a
   --  volatile state abstraction [(these are the Callable, Caller, Count, and
   --  Terminated attributes; see section
   --  :ref:`tasks-and-synchronization`)]. [An internal call to a protected
   --  function is treated like a call to a nonvolatile function if the
   --  function's Volatile_Function aspect is False.]

   type R is record
      F1 : Integer;
      F2 : Boolean;
   end record;

   type I is range 1 .. 10;

   type AI is array (I) of Integer;

   type AR is array (I) of R;

   V1 : Integer
     with Volatile, Async_Writers;

   V2 : R
     with Volatile, Async_Writers;

   V3 : AI
     with Volatile, Async_Writers;

   V4 : AR
     with Volatile, Async_Writers;


   procedure RV1 (X : out Integer)
     with Global => (Input => V1);

   procedure WV1 (X : in Integer)
     with Global => (Output => V1);



   procedure RV2 (X : out Boolean)
     with Global => (Input => V2);

   procedure WV2 (X : in Boolean)
     with Global => (In_Out => V2);



   procedure RV3 (X : out Integer)
     with Global => (Input => V3);

   procedure RV3UC (X : out Integer)
     with Global => (Input => V3);

   procedure WV3 (X : in Integer)
     with Global => (In_Out => V3);



   procedure RV4 (X : out Boolean)
     with Global => (Input => V4);

   procedure WV4 (X : in Boolean)
     with Global => (In_Out => V4);

   procedure RV4b (X : out Boolean)
     with Global => (Input => V4);



end Legal;
