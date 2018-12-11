package body P with Refined_State => (State => X) is

   X : Boolean := True;

   procedure Flip is
   begin
      --  Without seeing the refinement of State the following statement
      --  wouldn't work.
      X := not X;
   end;

end;
