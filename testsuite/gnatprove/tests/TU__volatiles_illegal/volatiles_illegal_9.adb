with System.Storage_Elements;

package body Volatiles_Illegal_9
  with SPARK_Mode
is
   procedure Embeded is
      --  TU: 5. The declaration of an effectively volatile object
      --  (other than as a formal parameter) shall be at library
      --  level. [That is, it shall not be declared within the scope
      --  of a subprogram body. An effectively volatile object has
      --  an external effect and therefore should be global even if it
      --  is not visible. It is made visible via a state abstraction.]

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
