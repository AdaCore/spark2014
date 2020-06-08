package body Test with
  SPARK_Mode
is

   procedure Set_Value (Ctx : in out Context)
   is
   begin
      Ctx.Value := Ctx.Value / 2;
   end Set_Value;

end Test;
