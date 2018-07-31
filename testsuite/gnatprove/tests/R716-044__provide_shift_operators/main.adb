with Types; use Types;

procedure Main with SPARK_Mode is
   X : T := 1;
begin
   X := Shift_Left (X, 1);
   pragma Assert (X = 2); --@ASSERT:PASS
   X := Shift_Right (X, 1);
   pragma Assert (X = 1); --@ASSERT:PASS
   X := Rotate_Right (X, 1);
   pragma Assert (X = 2 ** 31); --@ASSERT:PASS
   X := Rotate_Left (X, 1);
   pragma Assert (X = 1); --@ASSERT:PASS
end Main;
