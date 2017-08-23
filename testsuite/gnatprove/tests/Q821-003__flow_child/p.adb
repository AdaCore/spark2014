package body P
with
  Refined_State => (State => Data)
is
   Data : Boolean := True;

   procedure Flip is
   begin
      Data := not Data;
   end;

end;
