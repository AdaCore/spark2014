procedure Specexpr is
   function F return Boolean is
   begin
      return True;
   end F;
   type T (Disc : Boolean := F) is null record;
   X : T;
begin
   pragma Assert (X.Disc = True);
end;
