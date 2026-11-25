with Interfaces; use Interfaces;

procedure Image_Size_Bound
  (Signed_32 : Integer_32;
   Signed_64 : Integer_64;
   Modular_32 : Unsigned_32;
   Modular_64 : Unsigned_64;
   Low, High : Integer_32)
with SPARK_Mode
is
   subtype Dynamic is Integer_32 range Low .. High;

   S32 : constant String := Integer_32'Image (Signed_32);
   S64 : constant String := Signed_64'Image;
   M32 : constant String := Unsigned_32'Image (Modular_32);
   M64 : constant String := Modular_64'Img;
begin
   pragma Assert (S32'Length <= 11);
   pragma Assert (S64'Length <= 21);
   pragma Assert (M32'Length <= 11);
   pragma Assert (M64'Length <= 21);

   if Signed_32 in Dynamic then
      declare
         D : constant String := Dynamic'Image (Signed_32);
      begin
         pragma Assert (D'Length <= 11);
      end;
   end if;
end Image_Size_Bound;
