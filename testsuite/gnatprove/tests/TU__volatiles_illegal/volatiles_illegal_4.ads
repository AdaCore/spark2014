with System.Storage_Elements;

package Volatiles_Illegal_4
  --  TU: 14. As formal subprogram parameters of a Volatile type cannot have
  --  these aspects specified assumptions have to be made in the body of
  --  the subprogram of the properties that the formal parameter of a
  --  given mode may have as follows:
  --  * mode **in**: the formal parameter cannot be updated by the
  --    subprogram and is considered to have the properties
  --    Async_Writers => True and Effective_Reads => False. The actual
  --    parameter in a call must be Volatile and have these properties
  --    but may also have the properties Async_Readers and
  --    Effective_Writes set to True.
  --  * mode **out**: the formal parameter cannot be read by the
  --    subprogram as it is unknown whether a read will have an external
  --    effect. The formal parameter is considered to have the
  --    properties Async_Readers => True and/or Effective_Writes =>
  --    True. The actual parameter in a call to the subprogram must be
  --    Volatile and have either or both of these properties True but
  --    may also have Async_Writers and Effective_Reads set to True. If
  --    the subprogram attempts a read of the formal parameter a flow
  --    anomaly will be reported.
  --  * mode **in out**: the formal parameter is considered to have all
  --    properties; Async_Readers => True, Async_Writers => True,
  --    Effective_Reads => True, Effective_Writes => True. The actual
  --    parameter in a subprogram call must be Volatile and have all of
  --    these properties set to True.
  with SPARK_Mode
is
   A : Integer;

   B : Integer
     with Volatile,
          Address => System.Storage_Elements.To_Address (16#B0B0#);

   type Vol_Rec_T is record
      X : Integer := 0;
   end record with Volatile;

   Vol1 : Vol_Rec_T
     with Address => System.Storage_Elements.To_Address (16#ABC0#);

   Vol2 : Vol_Rec_T
     with Async_Writers,
          Address => System.Storage_Elements.To_Address (16#ABCD0#);

   procedure P1 (Par : in Vol_Rec_T ; Par2 : out Integer);
   --  Par must have Async_Writers => True and Effective_Reads => False.

   procedure P2 (Par : out Vol_Rec_T);
   --  Par must have Async_Readers => True.

   procedure P3 (Par : in out Vol_Rec_T);
   --  Par must have all attributes set to True.

   procedure P4 (X : in out Integer);
   --  The formal parameter is a non-Volatile so actual parameters
   --  must also be non-Volatiles.
end Volatiles_Illegal_4;
