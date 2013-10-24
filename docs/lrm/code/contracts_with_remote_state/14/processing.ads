with Raw_Data;
package Processing
  with Abstract_State => State
is
   procedure Read_Processed_Data (Value : out Integer)
     with Global  => (Input => (State, Raw_Data.State)),
          Depends => (Value => (State, Raw_Data.State)),
          Post    => Raw_Data.Data_Is_Valid (Value);

end Processing;
