package body P is

   procedure Identity (L : in out List; Cu : in out Cursor) is
   begin
      Insert (L, Cu, 1);
      Cu := (if Cu = No_Element then Last (L) 
             else Previous (L, Cu));
      Delete (L, Cu);
   end Identity;

   procedure Nearly_Identity (L : in out List; Cu : in out Cursor) is
      E : Element_Type := Element (L, Cu);
      Nxt : Cursor := Next (L, Cu);
   begin
      Delete (L, Cu);
      Insert (L, Nxt, E);
      Cu := (if Nxt = No_Element then Last (L)
             else Previous (L, Nxt));
   end Nearly_Identity;

end P;
