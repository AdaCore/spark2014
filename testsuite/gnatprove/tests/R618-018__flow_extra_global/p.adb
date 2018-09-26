package body P
  with Refined_State => (State1 => X, State2 => Extra.State2e)
is

   X : Integer := 0;

   package body Extra with Refined_State => (State2e => Extr) is
      Extr : Integer := 0;
      function Get return Integer is (Extr) with Refined_Global => Extr;
   end;

   procedure Dummy (Y : out Integer) with Refined_Global => X is
   -- this should be Refined_Global => (X, Extra.State2e)
   begin
      Y := X + Extra.Get;
   end;
end;
