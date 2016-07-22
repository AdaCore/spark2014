pragma SPARK_Mode;
procedure Get_Out_Subtype_Int (X, Y, Z : Integer) is

   procedure Controller_Get_Desired_Rate
     (Roll_Rate_Desired  : out Integer;
      Pitch_Rate_Desired : out Integer;
      Yaw_Rate_Desired   : out Integer)
   with Global => (X, Y, Z);

   procedure Controller_Get_Desired_Rate
     (Roll_Rate_Desired  : out Integer;
      Pitch_Rate_Desired : out Integer;
      Yaw_Rate_Desired   : out Integer) is
   begin
      Roll_Rate_Desired  := X;
      Pitch_Rate_Desired := Y;
      Yaw_Rate_Desired   := Z;
   end Controller_Get_Desired_Rate;

   subtype T_Rate is Integer range -3_000  .. 3_000;

   Roll_Rate_Desired   : T_Rate  := 0;
   Pitch_Rate_Desired  : T_Rate  := 0;
   Yaw_Rate_Desired    : T_Rate  := 0;

begin
   Controller_Get_Desired_Rate (Roll_Rate_Desired, Integer(Pitch_Rate_Desired),
                                T_Rate(Yaw_Rate_Desired));
end Get_Out_Subtype_Int;
