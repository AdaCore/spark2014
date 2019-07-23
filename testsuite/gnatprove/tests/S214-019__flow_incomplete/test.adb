package body Test
with
   Refined_State => (State => Last)
is
   procedure Is_Odd
      (Value  : Integer;
       Result : out Boolean)
   is
   begin
      Result := Value mod 2 = 1;
      Last   := Result;
   end Is_Odd;

end Test;
