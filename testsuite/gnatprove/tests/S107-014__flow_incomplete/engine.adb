package body Engine with
  Refined_State => (State => Dummy)
is
   Dummy : Boolean := True;

   ---------------
   -- Has_Piece --
   ---------------

   function Has_No_Piece return Boolean is (Dummy);

end Engine;
