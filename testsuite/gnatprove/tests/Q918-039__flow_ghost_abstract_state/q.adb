package body Q with Refined_State => (State => F) is
   F : Integer with Ghost;

   procedure Bar (X : Integer)
   is
   begin
      F := X; -- ghost global output
   end;
end;
