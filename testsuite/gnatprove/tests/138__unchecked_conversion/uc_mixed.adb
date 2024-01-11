package body UC_Mixed with SPARK_Mode is

   procedure Test (Val : REG1) is
      V : Buffer := UC_REG1( Val );
      W : REG1 := UC_REG1_Inv (V);
   begin
      pragma Assert ( V (1) = Val.F_Field1 );
      pragma Assert ( V (2) = Val.F_Field2 );
      pragma Assert ( V (3) = Val.F_Field3 );
      pragma Assert ( V (4) = Val.F_Field4 );
      pragma Assert (Val = W);
   end;

end uc_mixed;
