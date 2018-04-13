package body P with SPARK_Mode is

   procedure Do_Something
     (Buf : in out Buffer_Type;
      I   : in     Natural)
   is
      Temp : Interfaces.Unsigned_8 := Buf(Buf'First + I);
   begin
      Buf (Buf'First + I) := Temp + 1;
   end Do_Something;

end P;
