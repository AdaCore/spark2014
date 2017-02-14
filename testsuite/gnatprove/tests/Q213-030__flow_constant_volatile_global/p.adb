package body P with SPARK_Mode => Off
is

   Null_Info_Context : constant Info_Context := Info_Context'
     (String_Address => 0);

   procedure Clear_Context (Context : out Info_Context) is
   begin
      Context := Null_Info_Context;
   end;

end;
