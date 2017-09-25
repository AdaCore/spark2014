with External_Data;
pragma Elaborate_All(External_Data);

package Init_Data with
  SPARK_Mode
is
   pragma Elaborate_Body;
   Start_From_Zero     : Integer := 0;
   Start_From_Val      : Integer := External_Data.Val;
   Start_From_Zero_Bis : Integer;
   Start_From_Val_Bis  : Integer;
end Init_Data;
