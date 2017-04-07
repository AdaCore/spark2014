package body Discr
with SPARK_Mode
is
   procedure Test(Rec : in T_Record) is
      Data_Copy : T_Array := Rec.Data;
   begin
      pragma Assert (Data_Copy = Rec.Data);
   end Test;
end Discr;
