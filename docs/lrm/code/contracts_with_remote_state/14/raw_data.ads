package Raw_Data
   with Abstract_State => State
is

   function Data_Is_Valid (Value : Integer) return Boolean
      with Convention => Ghost;

   procedure Read (Value : out Integer)
      with Global  => (Input => State),
           Depends => (Value => State),
           Post    => Data_Is_Valid (Value);

end Raw_Data;
