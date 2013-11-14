package Raw_Data
--# own State;
--# Initializes State;
is

   function Data_Is_Valid return Boolean;
   --# global State;

   function Get_Value return Integer;
   --# global State;

   procedure Read_Next;
   --# global in out State;
   --# derives State from State;


end Raw_Data;
