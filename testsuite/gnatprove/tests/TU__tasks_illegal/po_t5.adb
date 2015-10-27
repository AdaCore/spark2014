package body PO_T5
  with Refined_State => (State => Wrong)
is
   Wrong : Integer;

   procedure Does_Nothing is
   begin
      null;
   end Does_Nothing;
end PO_T5;
