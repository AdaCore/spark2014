package body tq is

   procedure Array_Of_Array (Initial_Board : out Boards11)
   is
   begin

      Initial_Board :=
                (1 => ((White,Rook),
                                (White,Knight),
                                (White,Bishop),
                                (White,Queen),
                                (White,King),
                                (White,Bishop),
                                (White,Knight),
                                (White,Rook)
                                ),
                        2 => (Board_Index =>(White,Pawn)),
                        3 .. 6 => Empty_Row,
                        7 => (Board_Index =>(White,Pawn)),
                        8 => ((Black,Rook),
                                (Black,Knight),
                                (Black,Bishop),
                                (Black,Queen),
                                (Black,King),
                                (Black,Bishop),
                                (Black,Knight),
                                (Black,Rook)
                                )
                        )
                        ;

   end Array_Of_Array;

end tq;
