package Engine with
  Abstract_State => State
is
   function Has_No_Piece return Boolean;

   function Has_Piece return Boolean is (not Has_No_Piece);

end Engine;
