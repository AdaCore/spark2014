with Processing;
package Calculate is

   procedure Read_Calculated_Value (Value : out Integer)
      with Global  => (Input => (Processing.State, Raw_Data.State)),
           Depends => (Value => (Processing.State, Raw_Data.State)),
           Post    => Raw_Data.Data_Is_Valid (Value);

end Calculate;
