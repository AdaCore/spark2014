package body Fixed_Mem
  with SPARK_Mode
is
   Max : constant := 1000;
   type Data_Array is array (1 .. Max) of Integer;
   Data : Data_Array;
   Free : Natural;

   function Free_Memory return Natural is (Max - Free + 1);

   procedure Alloc is
      Free_Init : Natural with Ghost;

      procedure Check with Ghost is
      begin
         if Free <= Free_Init then
            raise Program_Error;
         end if;
      end Check;

   begin
      Free_Init := Free;
      -- some computations here
      Free := Free + 1;
      Check;
   end Alloc;

end Fixed_Mem;
