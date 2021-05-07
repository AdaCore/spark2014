procedure Signed is
   type S is new Short_Integer;
   pragma Provide_Shift_Operators (S);

   X : S := 253;
   Y : S;
begin
   --  Shift_Left

   Y := Shift_Left (X, 3);
   pragma Assert (Y = X * 2**3);

   Y := Shift_Left (-X, 3);
   pragma Assert (Y = (-X) * 2**3);

   Y := Shift_Left (X, 15);
   pragma Assert (Y = -2**15);

   Y := Shift_Left (X, 16);
   pragma Assert (Y = 0);

   --  Shift_Right

   Y := Shift_Right (X, 3);
   pragma Assert (Y = X / 2**3);

   Y := Shift_Right (-X, 3);
   pragma Assert (Y = 8160); -- (2**16 - X) / 2**3

   Y := Shift_Right (X, 7);
   pragma Assert (Y = 1);

   Y := Shift_Right (X, 8);
   pragma Assert (Y = 0);

   --  Shift_Right_Arithmetic

   Y := Shift_Right_Arithmetic (X, 3);
   pragma Assert (Y = X / 2**3);

   Y := Shift_Right_Arithmetic (-X, 3);
   pragma Assert (Y = (-X) / 2**3 - 1);

   Y := Shift_Right_Arithmetic (X, 7);
   pragma Assert (Y = 1);

   Y := Shift_Right_Arithmetic (X, 8);
   pragma Assert (Y = 0);

   --  Rotate_Left

   Y := Rotate_Left (X, 3);
   pragma Assert (Y = X * 2**3);

   Y := Rotate_Left (-X, 3);
   pragma Assert (Y = (-X) * 2**3 + 7);

   Y := Rotate_Left (X, 15);
   pragma Assert (Y = -2**15 + X / 2);

   Y := Rotate_Left (X, 16);
   pragma Assert (Y = X);

   --  Rotate_Right

   Y := Rotate_Right (X, 3);
   pragma Assert (Y = -24545);

   Y := Rotate_Right (-X, 3);
   pragma Assert (Y = 32736);

   Y := Rotate_Right (X, 7);
   pragma Assert (Y = -1535);

   Y := Rotate_Right (X, 8);
   pragma Assert (Y = -768);

   pragma Assert (False);  --  @ASSERT:FAIL

end;
