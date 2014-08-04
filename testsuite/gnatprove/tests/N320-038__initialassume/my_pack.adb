package body My_Pack
   with SPARK_Mode
is

   procedure Bump (X : in out Integer)
      with SPARK_Mode => Off
   is begin
      X := X + 1;
   end Bump;

   procedure Use_Bump is
   begin
      Bump (Z);

   end Use_Bump;

end My_Pack;
