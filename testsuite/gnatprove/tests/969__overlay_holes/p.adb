with Ada.Unchecked_Conversion;
procedure P with SPARK_Mode is
   type My_Bool is record
      C : Boolean;
   end record with Size => 32;
   for My_Bool use record
      C at 0 range 0 .. 0;
   end record;

   function Int_To_My_Bool is new Ada.Unchecked_Conversion (Integer, My_Bool);

   function Bad (X : aliased My_Bool) return Integer is
      Y : constant Integer with Import, Address => X'Address; --@UNCHECKED_CONVERSION:FAIL
   begin
      return Y;
   end Bad;

   C1 : aliased My_Bool := Int_To_My_Bool (0);
   C2 : aliased My_Bool := Int_To_My_Bool (2);
begin
   pragma Assert (C1 = C2);
   pragma Assert (Bad (C1) = Bad (C2));
end;
