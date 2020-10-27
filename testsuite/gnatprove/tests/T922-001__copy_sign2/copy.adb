procedure Copy is
   X : Float :=  1.5;
   Y : Float := -1.0;
   Z : Float :=  1.0;
begin
   pragma Assert (Float'Copy_Sign ( X, Y) = -1.5);   --@ASSERT:PASS
   pragma Assert (Float'Copy_Sign ( X, Z) =  1.5);   --@ASSERT:PASS
   pragma Assert (Float'Copy_Sign (-X, Z) =  1.5);   --@ASSERT:PASS
   pragma Assert (Float'Copy_Sign ( Y, Z) = -1.0);   --@ASSERT:FAIL
end Copy;
