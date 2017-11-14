with Interfaces.C; use Interfaces.C;

package body Stabilizer_Pack
with SPARK_Mode,
  Refined_State => (Asl_Parameters => (Asl_Err_Deadband,
                                       Asl_Alpha,
                                       Asl_Alpha_Long),
                    Asl_Variables => (Temperature,
                                      Pressure,
                                      Asl,
                                      Asl_Raw,
                                      Asl_Long))
is

   --  Private procedures and functions

   procedure Stabilizer_Alt_Hold_Update is
      Asl_Tmp      : Float;
      Asl_Long_Tmp : Float;
   begin
      Asl_Tmp := Asl * Asl_Alpha + Asl_Raw * (1.0 - Asl_Alpha);
      Asl_Long_Tmp := Asl_Long * Asl_Alpha_Long
        + Asl_Raw * (1.0 - Asl_Alpha_Long);
      if Pressure = 1.0 and Temperature = 25.0 and Asl_Err_Deadband = 0.0 then
         null;
      end if;

   end Stabilizer_Alt_Hold_Update;

end Stabilizer_Pack;
