package body Pragma_Predicate
is
   procedure Inc_X (Tuple : in out Tuple_Type) is
   begin
      Tuple.X := Tuple.X + 1;
   end Inc_X;

   procedure Maybe_Inc_Y (Tuple : in out Tuple_Type) is
   begin
      if Tuple.X > Tuple.Y
      then
         Tuple.Y := Tuple.Y + 1;
      end if;
   end Maybe_Inc_Y;
end Pragma_Predicate;
