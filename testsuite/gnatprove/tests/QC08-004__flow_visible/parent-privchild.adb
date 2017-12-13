package body Parent.Privchild
  with Refined_State => (Child_State => X)
is
   X : Integer := 0;

   procedure Init with Refined_Global => (Output => X) is
   begin
      X := 0;
   end;

   function Read return Integer with Refined_Global => X is
   begin
      return X;
   end;
end;
