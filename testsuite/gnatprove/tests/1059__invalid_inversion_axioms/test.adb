with Ada.Unchecked_Conversion;
procedure Test with SPARK_Mode is
   type Invalid_Source is record
      C : Character;
   end record with Size => 32;
   for Invalid_Source use record
      C at 0 range 0 .. 7;
   end record;

   type Invalid_Target is new Natural with Size => 32;

   function Conv_OK_1 is new Ada.Unchecked_Conversion (Invalid_Target, Integer);

   function Conv_Bad_1 is new Ada.Unchecked_Conversion (Integer, Invalid_Target);

   function Conv_Bad_2 is new Ada.Unchecked_Conversion (Invalid_Source, Integer);

   function Conv_OK_2 is new Ada.Unchecked_Conversion (Integer, Invalid_Source);

   procedure Test_1 (X : Integer) is
   begin
      pragma Assert (Conv_Ok_1 (Conv_Bad_1 (X)) = X); --  @ASSERT:FAIL
   end Test_1;

   procedure Test_2 (X : Integer) is
   begin
      pragma Assert (Conv_Bad_2 (Conv_OK_2 (X)) = X); --  @ASSERT:FAIL
   end Test_2;
begin
   null;
end;
