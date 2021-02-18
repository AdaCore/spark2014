package body P1 with Refined_State => (State1 => P2.State2) is
   package P2 with Abstract_State => State2 is
      procedure Dummy with Global => null;
   end P2;
   package body P2 with Refined_State => (State2 => X) is
      X : Boolean := True;
      procedure Dummy is null;
   end P2;
   procedure Dummy is null;
end P1;
