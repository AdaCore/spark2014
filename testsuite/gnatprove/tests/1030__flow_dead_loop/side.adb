pragma Extensions_Allowed (On);
function Side return Boolean is
   X : Boolean := True;
   function Flip return Boolean with Side_Effects is
   begin
      X := not X;
      return X;
   end;
begin
   if True then
      return True;
   else
      Y : Boolean := Flip;
      return Y;
   end if;
end;
