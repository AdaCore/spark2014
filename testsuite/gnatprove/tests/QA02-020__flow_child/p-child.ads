private package P.Child is
   X : Boolean := True with Part_Of => P.State;
   procedure Flip with Global => (In_Out => State);
end;
