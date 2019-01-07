with Engine; 	use Engine;

package CLI is

   procedure Pick_Up_Pice with
     Global => (In_Out => Engine.State),
     Pre => Has_No_Piece,
     Post => Has_Piece;

end CLI;
