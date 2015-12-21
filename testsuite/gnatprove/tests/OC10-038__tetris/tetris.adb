package body Tetris
is

   function Get_Y_After_Action (Y : Y_Coord; The_Action : Action)
                                return Y_Coord
   is (case The_Action is
       when Down => Y - 1,
       when others => Y)
   with Pre => True;

   function Foobar (Y : Y_Coord; The_Action : Action) return Y_Coord
   with Pre => True
   is
      tmp : y_Coord;
   begin
      if the_action = Down then
         tmp := y - 1;
      else
         tmp := y;
      end if;
      return tmp;
   end foobar;

end Tetris;
