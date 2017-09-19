package body Mem
  with SPARK_Mode,
  Refined_State => (State => (Data, Free, High))
is
   Max : constant := 1000;
   type Data_Array is array (1 .. Max) of Integer;
   Data : Data_Array;
   Free : Natural;
   High : Natural with Ghost;

   function Free_Memory return Natural is (Max - Free + 1);

   procedure Assign (From : in Natural; To : out Natural) with Ghost is
   begin
      To := From;
   end Assign;

   procedure Alloc is
      Free_Init : Natural with Ghost;
   begin
      Free_Init := Free;
      Assign (Free, Free_Init);
      -- some computations here
      Free := Free + 10;
      pragma Assert (Free > Free_Init);
   end Alloc;

end Mem;
