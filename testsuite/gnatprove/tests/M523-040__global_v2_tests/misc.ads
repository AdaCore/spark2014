package Misc
with Abstract_State => State
is

   procedure Test_01;
   --  proof in State

   function Test_02 return Boolean;
   --  in State

   procedure Test_03 (N : Integer);
   --  in out State

   procedure Test_04 (N : Integer);
   --  out State

end Misc;
