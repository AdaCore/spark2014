package body P1 with Refined_State => (State1 => (P2.State2, Z)) is
   Z : Boolean := True;
   package P2 with Abstract_State => State2, Initializes => State2 is
      procedure Flip2 with Global => (In_Out => (State2, Z));
   end P2;
   package body P2 with Refined_State => (State2 => (X, Y)) is
      X, Y : Boolean := True;
      procedure Flip2 is
      begin
         X := not X;
         Y := not Y;
         Z := not Z;
      end;
   end P2;
   procedure Flip1 is
   begin
      P2.Flip2;
   end;
end P1;
