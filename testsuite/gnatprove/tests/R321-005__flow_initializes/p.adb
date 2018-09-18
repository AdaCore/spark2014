package body P with Refined_State => (State1 => X,
                                      State2 => Y,
                                      State3 => null)
is
   X : Integer := 0;
   Y : Integer;
   procedure Dummy with Refined_Global => (Output => (X, Y)) is
   begin
      X := 0;
      Y := 0;
   end;
end;
