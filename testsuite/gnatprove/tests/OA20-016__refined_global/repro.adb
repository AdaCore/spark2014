package body Repro with
  Refined_State => (Game_State => Cur_Board)
is
   Cur_Board : Board;

   procedure Game_Reset
--    with Refined_Global => (Output => Cur_Board)
   is
   begin
      Cur_Board := (others => (others => Empty));
   end Game_Reset;

   function Get_Board return Board is (Cur_Board);

begin
   Game_Reset;
end Repro;
