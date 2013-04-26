package body P is

   procedure Identity_1 (L : in out Vector; Cu : in out Cursor) is
   begin
      Insert (L, Cu, 1);
      Cu := (if Cu = No_Element then Last (L) 
             else Previous (L, Cu));
      Delete (L, Cu);
   end Identity_1;

   procedure Identity_2 (L : in out Vector; Cu : in out Cursor) is
      E : Element_Type := Element (L, Cu);
      Nxt : Cursor := Next (L, Cu);
   begin
      Delete (L, Cu);
      Insert (L, Nxt, E);
      Cu := (if Nxt = No_Element then Last (L)
             else Previous (L, Nxt));
   end Identity_2;
   
   procedure Identity_Swap (L : in out Vector; Cu1 : Cursor; Cu2 : Cursor) is
      L_In : constant Vector := Copy (L);
   begin
      Swap (L, Cu1, Cu2);
      pragma Assert (Element (L, Cu1) = Element (L_In, Cu2));
      Swap (L, Cu1, Cu2);
   end Identity_Swap;

end P;
