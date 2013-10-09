package body P is pragma SPARK_Mode (On);

   procedure Identity (L : in out List; Cu : in out Cursor) is
   begin
      Insert (L, Cu, 1);
      Cu := (if Cu = No_Element then Last (L)
             else Previous (L, Cu));
      Delete (L, Cu);
   end Identity;

   procedure Nearly_Identity (L : in out List; Cu : in out Cursor) is
      E : Element_Type := Element (L, Cu);
      Prev : constant Cursor := Previous (L, Cu);
      Nxt : constant Cursor := Next (L, Cu);
   begin
      Delete (L, Cu);
      Insert (L, Nxt, E, Cu);
   end Nearly_Identity;

   procedure Identity_Swap (L : in out List; Cu1 : Cursor; Cu2 : Cursor) is
      L_In : constant List := Copy (L);
   begin
      Swap (L, Cu1, Cu2);
      pragma Assert (Element (L, Cu1) = Element (L_In, Cu2));
      Swap (L, Cu1, Cu2);
   end Identity_Swap;

   procedure Identity_Swap_Links (L : in out List; Cu1 : Cursor; Cu2 : Cursor)
   is
   begin
      Swap_Links (L, Cu1, Cu2);
      Swap_Links (L, Cu1, Cu2);
   end Identity_Swap_Links;

end P;
