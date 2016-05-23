package body Component_Size_Attribute
is
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
      pragma Assert (A2'Component_size >= 0);
      pragma Assert (A2'Component_size = 32); -- @ASSERT:FAIL
   end P;

   type R is null record;

   type RA is array (Positive range 1 .. 3) of R;

   procedure Test1 is
   begin
      pragma Assert (RA'Component_size >= 0);
      pragma Assert (RA'Component_size < 0); -- @ASSERT:FAIL
   end Test1;

   procedure Test2 is
   begin
      pragma Assert (Constrained_Array'Component_size >= 0);
      pragma Assert (Constrained_Array'Component_size < 0); -- @ASSERT:FAIL
   end Test2;

   procedure Test3 is
   begin
      pragma Assert (Unconstrained_Array'Component_Size >= 0);
      pragma Assert (Unconstrained_Array'Component_Size < 0); -- @ASSERT:FAIL
   end Test3;

   procedure Test4 is
   begin
      pragma Assert (CA'Component_Size >= 0);
      pragma Assert (CA'Component_Size = -6); -- @ASSERT:FAIL
   end Test4;

   procedure Test5 is
   begin
      pragma Assert (UA'Component_Size >= 0);
      pragma Assert (UA'Component_Size < 0); -- @ASSERT:FAIL
   end Test5;

begin

   null;

end Component_Size_Attribute;
