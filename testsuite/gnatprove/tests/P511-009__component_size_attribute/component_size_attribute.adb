procedure Component_Size_Attribute is
   pragma SPARK_Mode (On);

   subtype My_Integer is Integer range 1 .. 10;

   type Constrained_Array is array (My_Integer) of Natural;
   type Unconstrained_Array is array (Positive range <>) of Integer;

   CA : Constrained_Array := (others => 2);
   UA : Unconstrained_Array (1 .. 7) := (others => 1);

   procedure P (X : Integer) is

      type Array1 is array (1 .. X) of Integer;
      type Array2 is array (1 .. 1) of Array1;
      A1 : Array1 := (others => 1);
      A2 : Array2 := (others => A1);
   begin
      pragma Assert (A2'Component_Size >= 0);
      pragma Assert (A2'Component_size = 32); -- @ ASSERT:FAIL
   end P;

begin

   pragma Assert (Constrained_Array'Component_Size >= 0);
   pragma Assert (Unconstrained_Array'Component_Size >= 0);

   pragma Assert (CA'Component_Size >= 0);
   pragma Assert (CA'Component_Size = 32);

   pragma Assert (UA'Component_Size >= 0);

   pragma Assert (CA'Component_Size < 0); -- @ASSERT:FAIL

end Component_Size_Attribute;
