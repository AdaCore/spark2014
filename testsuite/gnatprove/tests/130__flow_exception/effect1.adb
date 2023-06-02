procedure Effect1 (X : Boolean; Y : out Boolean)
  with Depends => (Y => X)
is
   procedure Test (A : aliased out Boolean)
     with Exceptional_Cases =>
            (Program_Error    => True,
             Constraint_Error => True),
          Depends => (A => null, null => X)
   is
   begin
      --  Dummy effect, just to enable analysis of effective statements
      A := True;

      if X then
         raise Program_Error;
      else
         raise Constraint_Error;
      end if;
   end Test;

   A : aliased Boolean;

begin
   Test (A);
   Y := X;
exception
   when Program_Error =>
      Y := True;
   when Constraint_Error =>
      Y := False;
end;
