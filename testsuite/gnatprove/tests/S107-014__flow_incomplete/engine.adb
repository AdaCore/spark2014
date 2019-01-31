package body Engine with
  Refined_State => (State => Dummy)
is
   Dummy : Boolean := True;

   function Has_No_Piece return Boolean is (Dummy);

end Engine;
