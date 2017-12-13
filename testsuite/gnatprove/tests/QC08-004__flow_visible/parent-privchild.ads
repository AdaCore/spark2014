private package Parent.Privchild
   with Abstract_State => (Child_State with Part_Of => State)
is
   function Read return Integer with Global => Child_State;

   procedure Init               with Global => (Output => Child_State);
   --  This procedure is only to silence a warning that Child_State
   --  can't be initialized.
end;
