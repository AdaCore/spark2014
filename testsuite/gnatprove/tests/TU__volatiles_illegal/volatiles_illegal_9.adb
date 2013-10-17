with System.Storage_Elements;

package body Volatiles_Illegal_9
  with SPARK_Mode
is
   procedure Embeded is
      --  TU: 5. The declaration of a Volatile object (other than as a formal
      --  parameter) shall be at library level. [That is, it shall not be
      --  declared within the scope of a subprogram body. A Volatile variable
      --  has an external effect and therefore should be global even if it is
      --  not visible. It is made visible via a state abstraction.]

      Emb_Vol : Integer
        with Volatile,
             Async_Readers,
             Address => System.Storage_Elements.To_Address (16#C01D0#);
      --  Volatile object is not at library level.
   begin
      null;
   end Embeded;
begin
   --  TU: 13. Contrary to the general |SPARK| rule that expression evaluation
   --  cannot have side effects, a read of a Volatile object with the
   --  properties Async_Writers or Effective_Reads set to True is
   --  considered to have an effect when read. To reconcile this
   --  discrepancy, a name denoting such an object shall only occur in
   --  the following contexts:
   --  * as the name on the left-hand side of an assignment statement; or
   --  * as the [right-hand side] expression of an assignment statement; or
   --  * as the expression of an initialization expression of an object
   --    declaration; or
   --  * as an actual parameter in a call to an instance of
   --    Unchecked_Conversion whose result is renamed [in an object renaming
   --    declaration]; or
   --  * as an actual parameter in a procedure call of which the corresponding
   --    formal parameter is of a non-scalar Volatile type.
   if Vol + 5 > 0 then  --  Cannot have Vol appear here because expressions
                        --  cannot have side effects.
      A := 0;
   end if;
end Volatiles_Illegal_9;
