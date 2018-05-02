procedure Formals_Arr_Split (X, Y : Positive; B1, B2 : Boolean) with SPARK_Mode is
   type My_Array is array (Integer range <>) of Natural;
   subtype Constr_Arr is My_Array (0 .. X);

   subtype Constr_Arr_2 is My_Array (0 .. Y);

   subtype My_Index is Integer range 0 .. Y;
   type My_Array_3 is array (My_Index range <>) of Natural;

   procedure P (A : out Constr_Arr) with
     Pre => True
   is
   begin
      A := (0 .. X => 1);
   end P;

   procedure P2 (A : out Constr_Arr_2)
   is
   begin
      A := (0 .. Y => 1); -- @LENGTH_CHECK:FAIL
   end P2;

   procedure P3 (A : out Constr_Arr_2)
   is
   begin
      A := (0 .. Y => 1); -- @LENGTH_CHECK:FAIL
   end P3;

   procedure F (A : in out My_Array_3) with Pre => A'Length > 0 is
   begin
      A (A'First) := 1;
   end F;

   procedure F (A : in out My_Array) with Pre => A'Length > 0 is
   begin
      F (My_Array_3 (A)); -- @RANGE_CHECK:FAIL
   end F;

   V : Constr_Arr := (others => 1);
   U : Constr_Arr_2 := (others => 1);
begin
   P (V);
   P2 (U);
   if B1 then
      if B2 then
         P (U); -- @LENGTH_CHECK:FAIL
      else
         P2 (V);
      end if;
   else
      if B2 then
         P (My_Array (U)); -- @LENGTH_CHECK:FAIL
      else
         P3 (My_Array (V));
      end if;
   end if;
end Formals_Arr_Split;
