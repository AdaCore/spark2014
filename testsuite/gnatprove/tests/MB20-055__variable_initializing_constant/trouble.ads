package Trouble
  with SPARK_Mode => On,
       Initializes => V
is
   --  Front end spots potential access-before-elaboration here,
   --  so warns need for pragma Elaborate_Body here
   pragma Elaborate_Body;

   --  V declared here, but assumed to be initialized in the body
   V : Integer;

   --  Force need for a body
   procedure Op (X : in out Boolean)
     with Depends => (X => X);
end Trouble;
