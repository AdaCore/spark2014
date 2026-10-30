with Interfaces;

procedure Image_Size_Bounds with SPARK_Mode is
   Signed_Image : constant String :=
     Interfaces.Integer_64'Image (Interfaces.Integer_64'First);
   Modular_Image : constant String :=
     Interfaces.Unsigned_64'Image (Interfaces.Unsigned_64'Last);
begin
   pragma Assert (Signed_Image'Length <= 32);
   pragma Assert (Modular_Image'Length <= 32);

   pragma Assert (Signed_Image'Length <= 3); -- @ASSERT:FAIL
   pragma Assert (Modular_Image'Length <= 3); -- @ASSERT:FAIL
end Image_Size_Bounds;
