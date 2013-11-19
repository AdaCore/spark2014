with Raw_Data;

package Processing
  with SPARK_Mode,
       Abstract_State => State
is
   procedure Get_Processed_Data (Value : out Integer)
     with Global  => (Input  => Raw_Data.State,
                      In_Out => State),
          Depends => ((Value,
                       State) => (State,
                                  Raw_Data.State)),
          Pre     => Raw_Data.Data_Is_Valid;
end Processing;
