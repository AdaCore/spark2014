package body Calculate
  with SPARK_Mode
is
   procedure Read_Calculated_Value (Value : out Integer) is
   begin
      Processing.Get_Processed_Data (Value);
   end Read_Calculated_Value;
end Calculate;
