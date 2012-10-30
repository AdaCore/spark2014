
package body Processing
is

   State : Integer;

   procedure Read_Processed_Data (Value : out Integer)
   is
      Local_Value : Integer;
   begin
      Raw_Data.Read (Local_Value);
      Value := State + Local_Value;
   end Read_Processed_Data;

end Processing;