procedure Main
  with
    SPARK_Mode => On
is
   --  This is fine, OK_I2 can only have a valid value
   OK_I1  : aliased constant Positive := 15 with Alignment => 4;
   OK_I2  : aliased constant Integer with Address => OK_I1'Address, Import, Alignment => 4;

   --  Same for an input parameter
   type My_Pos is new Positive with Alignment => 4, Size => 31;
   function OK_F (I1 : aliased My_Pos) return Integer with
     Global => null
   is
      I2 : aliased constant Integer with Address => I1'Address, Import, Alignment => 4;
   begin
      return I2;
   end OK_F;

   --  This is incorrect as Bad_I2 has an invalid value
   Bad_I1 : aliased constant Integer := -15 with Alignment => 4;
   Bad_I2 : aliased constant Positive with Address => Bad_I1'Address, Import, Alignment => 4;

   --  Same for an input parameter
   type My_Int is new Integer with Alignment => 4, Size => 32;
   function Bad_F (I1 : aliased My_Int) return Positive with
     Global => null
   is
      I2 : aliased constant Positive with Address => I1'Address, Import, Alignment => 4;
   begin
      return I2;
   end Bad_F;
begin
   null;
end Main;
