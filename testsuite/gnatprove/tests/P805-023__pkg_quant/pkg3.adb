package body Pkg3 with SPARK_Mode => On is

   X : Integer;

   function F return Integer is
   begin
      return X;
   end F;

   function G (Z : Integer) return Integer is
   begin
      return Z / 2;
   end G;

begin
   pragma SPARK_Mode (Off);
   L : for I in Integer loop
      if G (I) = I then
         X := X + 1;
      end if;
   end loop L;
end;
