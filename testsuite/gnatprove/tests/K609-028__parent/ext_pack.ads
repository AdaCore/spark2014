package Ext_Pack
  with Abstract_State => S,
       Initializes => (C, S)
is

   C : Integer := 0;

   procedure Result;

end Ext_Pack;
