package Repro with
    Abstract_State => Game_State,
    Initializes    => Game_State
is
   type Cell is (Empty, I, O, J, L, S, T, Z);

   subtype X_Coord is Integer range 1 .. 10;
   subtype Y_Coord is Integer range 1 .. 20;

   type Line is array (X_Coord) of Cell with Pack;
   type Board is array (Y_Coord) of Line;

   function Is_Empty (B : Board) return Boolean is
     (for all Y in Y_Coord => (for all X in X_Coord => B (Y)(X) = Empty))
     with Ghost;

   function Get_Board return Board
   with Global => (Input => Game_State);

   procedure Game_Reset
   with
     Global => (Output => Game_State),
     Post   => Is_Empty (Get_Board);
end Repro;
