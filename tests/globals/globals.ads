package Globals
--# own G;
is

   G : Integer;

   function Direct_Read return Integer;
   --# global in G;

   procedure Direct_Write;
   --# global out G;

   procedure Direct_Read_Write;
   --# global in out G;

   function Indirect_Read return Integer;
   --# global in G;

   procedure Indirect_Write;
   --# global out G;

   procedure Indirect_Read_Write;
   --# global in out G;

end Globals;
