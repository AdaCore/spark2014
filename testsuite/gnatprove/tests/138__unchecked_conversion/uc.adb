package body UC with SPARK_Mode is

   procedure Test (Val : REG1) is
      V : NvU32 := UC_REG1( Val );
      W : REG1 := UC_REG1_Inv (V);
   begin
      pragma Assert ( ( UC_REG1( Val ) and 16#0000_00FF# ) = NvU32 (Val.F_Field1 ));
      pragma Assert ( ( UC_REG1( Val ) and 16#0000_0F00# ) / 256 = NvU32 (Val.F_Field2 ));
      pragma Assert ( ( UC_REG1( Val ) and 16#0001_0000# ) / 65536 = NvU32 (Val.F_Field3 ));
      pragma Assert ( ( UC_REG1( Val ) and 16#000E_0000# ) / 131072 = NvU32 (Val.F_Field4 ));

      pragma Assert (Val = W);
   end;

end UC;
