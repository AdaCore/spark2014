package tq is

        Board_Size : constant Integer :=8;
        type Board_Index is range 1 .. Board_Size;
        type Colours is (No_colour, Black, White);
        type Pieces is (No_Piece, Pawn, Knight, Rook, Bishop, Queen, King);
        type Contents is record
              Colour : Colours;
              Piece : Pieces;
        end record;
        type Row is array (Board_Index) of Contents;
        type Boards11 is array (Board_Index) of Row;
        Empty : constant Contents := (No_Colour, No_Piece);
        Empty_Row : Constant Row := (Board_Index => Empty);

        procedure Array_Of_Array (Initial_Board : out Boards11);
        --procedure Multi_Dim_Array (P, Q : out Complex);
end tq;

