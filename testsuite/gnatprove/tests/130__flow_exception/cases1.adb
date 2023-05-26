procedure Cases1 (X : Integer)
  with Global => null
is
   A, B : Boolean;

   procedure Test
     with Exceptional_Cases =>
            (Program_Error    => A,   --  A is initialized in the body
             Constraint_Error => B),  --  B is not initialized in the body
          Global => (Input => X, In_Out => A, Proof_In => B)
   is
   begin
      if X > 0 then
         A := True;
         raise Program_Error;
      elsif X < 0 then
         raise Constraint_Error;
      else
         pragma Assert (X = 0);
      end if;
   end Test;

begin
   Test;
exception
   when Program_Error | Constraint_Error =>
      null;
end;
