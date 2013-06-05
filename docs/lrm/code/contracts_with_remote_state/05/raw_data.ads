package Raw_Data
--# own State;
is

   --# function Data_Is_Valid (Value : Integer) return Boolean;

   procedure Read (Value : out Integer);
   --# global in State;
   --# derives Value from State;
   --# post Data_Is_Valid (Value);

end Raw_Data;