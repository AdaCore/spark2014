package P with Abstract_State => State is
   procedure Main with Global => State;
   --  The Global & Refined_Global are only to trigger an extra message about
   --  an unknown object missing from both contracts.
end;
