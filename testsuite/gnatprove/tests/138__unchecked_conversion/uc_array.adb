package body UC_Array with SPARK_Mode is

   procedure Test (Val : REG1) is
      V : NvU32 := UC_REG1( Val );
      W : REG1 := UC_REG1_Inv (V);
   begin
      pragma Assert ( ( UC_REG1( Val ) and 16#0000_00FF# ) = NvU32 (Val(1) ));
      pragma Assert ( ( UC_REG1( Val ) and 16#0000_FF00# ) / 256 = NvU32 (Val(2) ));
      pragma Assert ( ( UC_REG1( Val ) and 16#00FF_0000# ) / 65536 = NvU32 (Val(3) ));
      pragma Assert ( ( UC_REG1( Val ) and 16#FF00_0000# ) / 2**24 = NvU32 (Val(4) ));

      pragma Assert (Val = W);
   end;

end UC_Array;
