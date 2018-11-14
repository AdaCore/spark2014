package body GP with Refined_State => (State => X) is
   X : Boolean := True;
   procedure Flip with Refined_Global => (In_Out => X) is
   begin
      X := not X;
   end;
end;
