pragma SPARK_Mode;
procedure Get_Out_Subtype (X, Y, Z : Float) is

   procedure Controller_Get_Desired_Rate
     (Roll_Rate_Desired  : out Float;
      Pitch_Rate_Desired : out Float;
      Yaw_Rate_Desired   : out Float)
   with Global => (X, Y, Z);

   procedure Controller_Get_Desired_Rate
     (Roll_Rate_Desired  : out Float;
      Pitch_Rate_Desired : out Float;
      Yaw_Rate_Desired   : out Float) is
   begin
      Roll_Rate_Desired  := X;
      Pitch_Rate_Desired := Y;
      Yaw_Rate_Desired   := Z;
   end Controller_Get_Desired_Rate;

   subtype T_Rate is Float range -3_000.0  .. 3_000.0;

   Roll_Rate_Desired   : T_Rate  := 0.0;
   Pitch_Rate_Desired  : T_Rate  := 0.0;
   Yaw_Rate_Desired    : T_Rate  := 0.0;

begin
   Controller_Get_Desired_Rate (Roll_Rate_Desired, Pitch_Rate_Desired,
                                Yaw_Rate_Desired);
end Get_Out_Subtype;
