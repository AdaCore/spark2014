package body P with Refined_State => (State => A) is
   A : Boolean := True;
   procedure Proc (X : out Boolean) is
   begin
      A := not A;
   end;
end;
