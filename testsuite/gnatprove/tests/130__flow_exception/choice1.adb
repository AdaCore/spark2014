procedure Choice1 (X : Boolean; Y : out Boolean)
  with Post => Y = X,
       Depends => (Y => X)
is
   E1 : exception;
   E2 : exception;

   procedure Depends (Cond : Boolean)
      with Exceptional_Cases => (E1 => Cond, E2 => not Cond)
   is
   begin
      if Cond then
         raise E1;
      else
         raise E2;
      end if;
   end;

begin
   Depends (X);
   raise Program_Error;
exception
   when E1 =>
      Y := True;
   when E2 =>
      Y := False;
end;
