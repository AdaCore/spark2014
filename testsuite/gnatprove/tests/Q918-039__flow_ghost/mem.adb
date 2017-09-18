package body Mem
  with SPARK_Mode
is
   Prev : Natural;

   procedure Assign (From : in Natural; To : out Natural) with Ghost is
   begin
      Prev := From;
      To := From;
   end Assign;

   procedure Alloc is
      X, Y : Natural := 0 with Ghost;
   begin
      Assign (X, Y);
   end Alloc;

end Mem;
