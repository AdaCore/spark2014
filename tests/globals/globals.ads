package Globals
--# own G;
is

   G : Integer;

   function Direct_Read return Integer;

   procedure Direct_Write;

   procedure Direct_Read_Write;
   pragma Precondition (G < Integer'Last);

   function Indirect_Read return Integer;

   procedure Indirect_Write;

   procedure Indirect_Read_Write;
   pragma Precondition (G < Integer'Last);

end Globals;
