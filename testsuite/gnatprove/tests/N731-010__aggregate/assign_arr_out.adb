procedure Assign_Arr_Out with
  SPARK_Mode
is
   type Array_Type is array (Positive range <>) of Integer;

   procedure Assign_Array (A : out Array_Type) is
   begin
      A := (84, 36);
   end Assign_Array;

   A : Array_Type (1 .. 2);
begin
   Assign_Array (A);
end Assign_Arr_Out;
