procedure Access_Inline
  with SPARK_Mode
is
   type T_Float32 is digits 6  range -3.40282E+38 .. 3.40282E+38;
   for T_Float32'Size use 32;
   C_2Pi_In_Degrees : constant T_Float32 := 360.0;
   subtype T_Angle_360 is T_Float32 range 0.0 .. C_2Pi_In_Degrees;
   type T_M_ID is (M1, M2, M3, M4);
   type T_ANGLE is array (T_M_ID) of T_Angle_360;

   ANGLE        : T_ANGLE := (others => 0.0);

   procedure S_COMPUTE
     (ANGLE           : in out  T_FLOAT32
     )
   is
   begin
      ANGLE := ANGLE - ANGLE;
   end S_COMPUTE;

begin
   S_COMPUTE (ANGLE(M4));
end Access_Inline;
