package body Full
   with SPARK_Mode
is

   procedure Bump (X : in out Integer)
   is begin
      X := X + 1;
   end Bump;

   procedure Use_Bump is
   begin
      Bump (Z);
   end Use_Bump;

end Full;
