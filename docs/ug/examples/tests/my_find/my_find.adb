function My_Find (L : List; E : Element_Type) return Cursor with
  SPARK_Mode
is
   Cu : Cursor := First (L);

begin
   while Has_Element (L, Cu) loop
      pragma Loop_Invariant (for all I in 1 .. P.Get (Positions (L), Cu) - 1 =>
                                Element (Model (L), I) /= E);

      if Element (L, Cu) = E then
         return Cu;
      end if;

      Next (L, Cu);
   end loop;

   return No_Element;
end My_Find;
