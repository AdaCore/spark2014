procedure Main with SPARK_Mode is
   type My_Arr is array (Positive range 1 .. 10) of Integer;

   function F return My_Arr is
   begin
      return (1 .. 10 => 0);
   end F;

   function G return Boolean is
     (for all E of F => E = 0);

   X : My_Arr := F;
begin
   pragma Assert (for all E of X => E = 0);
end Main;
