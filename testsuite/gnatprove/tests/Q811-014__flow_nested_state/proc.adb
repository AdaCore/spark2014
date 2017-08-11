procedure Proc is

   package Nested with Abstract_State => State is
      function Get return Boolean with Post => Get'Result;
   private
      X : Boolean := True with Part_Of => State;
   end;

   package body Nested with Refined_State => (State => X) is
      function Get return Boolean is (X);
   end;

begin
   pragma Assert (Nested.Get);
end;
