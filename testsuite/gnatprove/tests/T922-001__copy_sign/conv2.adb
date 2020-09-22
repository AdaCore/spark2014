with Unchecked_Conversion;
procedure Conv is
   type Float_Bytes is
     array (1 .. Float'Size / 8) of Integer range 0 .. 255 with
      Component_Size => 8,
      Size           => Float'Size;

   function To_Bytes is new Unchecked_Conversion (Float, Float_Bytes);

   function Zero return Float is (0.0);

   Z1 : Float := Zero;
   Z2 : Float := -Zero;

   Z1_Bytes : constant Float_Bytes := To_Bytes (Z1);
   Z2_Bytes : constant Float_Bytes := To_Bytes (Z2);
begin
   pragma Assert (Z1_Bytes = Z1_Bytes); --@ASSERT:FAIL
end Conv;
