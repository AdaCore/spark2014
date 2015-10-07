with Init_Data;
pragma Elaborate_All (Init_Data);
package Use_Data with
  SPARK_Mode,
  Initializes => (S0  => Init_Data.Start_From_Zero,
                  SV  => Init_Data.Start_From_Val,
                  S0b => Init_Data.Start_From_Zero_Bis,
                  SVb => Init_Data.Start_From_Val_Bis)
is
   S0  : Integer := Init_Data.Start_From_Zero;
   SV  : Integer := Init_Data.Start_From_Val;
   S0b : Integer := Init_Data.Start_From_Zero_Bis;
   SVb : Integer := Init_Data.Start_From_Val_Bis;
end Use_Data;
