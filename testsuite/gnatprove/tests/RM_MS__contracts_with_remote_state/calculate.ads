with Processing,
     Raw_Data;

package Calculate
  with SPARK_Mode
is
   procedure Read_Calculated_Value (Value : out Integer)
     with Global  => (In_Out => Processing.State,
                      Input  => Raw_Data.State),
          Depends => ((Value,
                       Processing.State) => (Processing.State,
                                             Raw_Data.State)),
          Pre     => Raw_Data.Data_Is_Valid;
end Calculate;
