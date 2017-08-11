package body Pkg is

   package body Nested with Refined_State => (State => X) is
      function Get return Boolean is (X);
   end;

begin
   pragma Assert (Nested.Get);
end;
