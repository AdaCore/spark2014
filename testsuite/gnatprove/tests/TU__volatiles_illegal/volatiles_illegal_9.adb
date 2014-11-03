with System.Storage_Elements;

package body Volatiles_Illegal_9
  with SPARK_Mode
is
   procedure Embeded is
      --  TU: 5. The declaration of an effectively volatile
      --  stand-alone object shall be a library-level declaration. [In
      --  particular, it shall not be declared within a subprogram.]

      Emb_Vol : Integer
        with Volatile,
             Async_Readers,
             Address => System.Storage_Elements.To_Address (16#C01D0#);
      --  Volatile object is not at library level.
   begin
      null;
   end Embeded;
begin
   if Vol + 5 > 0 then  --  Cannot have Vol appear here because expressions
                        --  cannot have side effects.
      A := 0;
   end if;
end Volatiles_Illegal_9;
