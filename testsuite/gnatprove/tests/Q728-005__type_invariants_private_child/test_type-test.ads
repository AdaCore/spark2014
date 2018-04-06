private package Test_Type.Test with SPARK_Mode is
   X : constant T := (F => 0);

   function Decr_Int_2 (X : T) return T is
     (F => X.F - 1)
   with Pre => X.F > Integer'First;
   Y : T := Decr_Int (X) with Part_Of => A_State;
   pragma Assert (X = Y); --@ASSERT:FAIL
end Test_Type.Test;
