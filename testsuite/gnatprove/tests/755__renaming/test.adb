procedure Test with SPARK_Mode is

   type My_Array is array (Positive range <>) of Integer;

   type My_Array_Acc is not null access My_Array;

   procedure Do_Loop (A : My_Array_Acc) is
   begin
      for I in A'Range loop
         declare
            Val renames A (I);
         begin
            Val := 2;
         end;
      end loop;
   end Do_Loop;

   procedure Do_Loop_2 (B : in out My_Array_Acc) is
      A : constant access My_Array := B;
   begin
      for I in A'Range loop
         declare
            Val renames A (I);
         begin
            Val := 2;
         end;
      end loop;
   end Do_Loop_2;

begin
   null;
end;
