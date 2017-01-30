package body Remote1 with Refined_State => (State => Inner) is

   Inner : Integer := 0;

   function Foo return Integer is (Inner);

end;
