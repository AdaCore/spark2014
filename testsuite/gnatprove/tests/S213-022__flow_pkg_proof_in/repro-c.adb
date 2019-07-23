package body Repro.C
with Refined_State => (State => Y)
is
   Y : Byte := 0;

   function Invariant return Boolean
   is (Get_Foo > 0 and Y = 0);

end Repro.C;
