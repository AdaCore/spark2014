package Globals is

   --  Global variables used to show state annotations
   D2 : Integer := 41;
   D1 : Integer;
   D3 : Integer := 0;

   --  Global variables used to show global annotations
   W1      : Integer;
   R1, RW1 : Integer := 0;

   --  Package-level procedure used to show global annotations
   procedure Proc (Cond : Boolean);

end Globals;
