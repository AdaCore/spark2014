
package body Calculate
is

   procedure Read_Calculated_Value (Value : out Integer)
   is
   begin
      Processing.Read_Processed_Data (Value);
   end Read_Calculated_Value;

end Calculate;