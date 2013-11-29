with System.Storage_Elements;

package Multiple_Ports
  with SPARK_Mode
is
   type Volatile_Type is record
      I : Integer;
   end record with Volatile;

   --  This type declaration indicates all objects of this type will
   --  be volatile. We can declare a number of objects of this type
   --  with different properties.

   --  V_In_1 is essentially an external input since it has
   --  Async_Writers => True but Async_Readers => False. Reading a
   --  value from V_In_1 is independent of other reads of the same
   --  object. Two successive reads might not have the same value.
   V_In_1 : Volatile_Type
     with Async_Writers,
          Address => System.Storage_Elements.To_Address (16#A1CAF0#);

   --  V_In_2 is similar to V_In_1 except that each value read is
   --  significant. V_In_2 can only be used as a Global with a
   --  mode_Selector of Output or In_Out or as an actual parameter
   --  whose corresponding formal parameter is of a Volatile type and
   --  has mode out or in out.
   V_In_2 : Volatile_Type
     with Async_Writers,
          Effective_Reads,
          Address => System.Storage_Elements.To_Address (16#ABCCAF0#);


   --  V_Out_1 is essentially an external output since it has
   --  Async_Readers => True but Async_Writers => False. Writing the
   --  same value successively might not have an observable effect.
   V_Out_1 : Volatile_Type
     with Async_Readers,
          Address => System.Storage_Elements.To_Address (16#BBCCAF0#);

   --  V_Out_2 is similar to V_Out_1 except that each write to
   --  V_Out_2 is significant.
   V_Out_2 : Volatile_Type
     with Async_Readers,
          Effective_Writes,
          Address => System.Storage_Elements.To_Address (16#ADACAF0#);

   --  This declaration defaults to the following properties:
   --    Async_Readers    => True,
   --    Async_Writers    => True,
   --    Effective_Reads  => True,
   --    Effective_Writes => True;
   --  That is the most comprehensive type of external interface which
   --  is bi-directional and each read and write has an observable
   --  effect.
   V_In_Out : Volatile_Type
     with Address => System.Storage_Elements.To_Address (16#BEECAF0#);

   --  These volatile variable declarations may be used in specific
   --  ways as global items and actual parameters of subprogram calls
   --  depend on their properties.

   procedure Read (Value : out Integer)
     with Global  => (Input => V_In_1),
          Depends => (Value => V_in_1);
   --  V_In_1, V_Out_1 and V_Out_2 are compatible with a mode selector
   --  of Input as this mode requires Effective_Reads => False.

   procedure Write (Value : in Integer)
     with Global  => (Output => V_Out_1),
          Depends => (V_Out_1 => Value);
   --  Any Volatile Global is compatible with a mode selector of
   --  Output. A flow error will be raised if the subprogram attempts
   --  to read a Volatile Global with Async_Writers and/or
   --  Effective_Reads set to True.

   procedure Read_With_Effect (Value : out Integer)
     with Global  => (In_Out => V_In_2),
          Depends => (Value  => V_In_2,
                      V_In_2 => null);
   --  Any Volatile Global is compatible with a mode selector of
   --  In_Out. The Depends aspect is used to specify how the Volatile
   --  Global is intended to be used and this is checked by flow
   --  analysis to be compatible with the properties specified for the
   --  Volatile Global.

   --  When a formal parameter is volatile, assumptions have to be
   --  made in the body of the subprogram as to the possible
   --  properties that the actual volatile parameter might have
   --  depending on the mode of the formal parameter.

   procedure Read_Port (Port : in Volatile_Type; Value : out Integer)
     with Depends => (Value => Port);
   --  Port is Volatile and of mode in. Assume that the formal
   --  parameter has the properties Async_Writers => True and
   --  Effective_Reads => False. The actual parameter in a call of the
   --  subprogram must have Async_Writers => True and
   --  Effective_Reads => False and may have Async_Writers and/or
   --  Effective_Writes set to True. As an in mode parameter it can
   --  only be read by the subprogram.
   --  Eg. Read_Port (V_In_1, Read_Value).

   procedure Write_Port (Port : out Volatile_Type; Value : in Integer)
     with Depends => (Port => Value);
   --  Port is volatile and of mode out. Assume the formal parameter
   --  has the properties Async_Readers => True and
   --  Effective_Writes => True. The actual parameter in a call to the
   --  subprogram must have Async_Readers and/or Effective_Writes
   --  True, and may have Async_Writers and Effective_Reads True. As
   --  the mode of the formal parameter is mode out, it is
   --  incompatible with reading the parameter because this could read
   --  a value from an Async_Writer. A flow error will be signalled if
   --  a read of the parameter occurs in the subprogram.
   --  Eg. Write_Port (V_Out_1, Output_Value) and
   --      Write_Port (V_Out_2, Output_Value).

   --  A Volatile formal parameter type of mode in out is
   --  assumed to have all the properties True:
   --    Async_Readers    => True,
   --    Async_Writers    => True,
   --    Effective_Reads  => True,
   --    Effective_Writes => True;
   --  The corresponding actual parameter in a subprogram call must be
   --  volatile with all of the properties set to True.
   procedure Read_And_Ack (Port : in out Volatile_Type; Value : out Integer)
     with Depends => (Value => Port,
                      Port  => Port);
   --  Port is Volatile and reading a value may require the sending of
   --  an acknowledgement, for instance.
   --  Eg. Read_And_Ack (V_In_Out, Read_Value).

end Multiple_Ports;
