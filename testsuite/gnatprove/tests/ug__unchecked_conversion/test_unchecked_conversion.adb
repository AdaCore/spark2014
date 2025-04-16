with Ada.Unchecked_Conversion;

procedure Test_Unchecked_Conversion with SPARK_Mode is

   function Bad_Size is new Ada.Unchecked_Conversion (Boolean, Character);

   type With_Holes is record
      B : Boolean;
   end record with Size => 8;

   function To_Chars is new Ada.Unchecked_Conversion (With_Holes, Character);

begin
   null;
end Test_Unchecked_Conversion;
