package body P is pragma SPARK_Mode (On);

   procedure Identity (L : in out Set; E : Element_Type) is
      Cu : Cursor;
      I : Boolean;
   begin
      Insert (L, E, Cu, I);
      pragma Assert (I);
      Delete (L, Cu);
   end Identity;

   procedure Nearly_Identity (L : in out Set; Cu : in out Cursor) is
      E : Element_Type := Element (L, Cu);
      I : Boolean;
      Old_K : constant Formal_Model.E.Sequence := Elements (L) with Ghost;
   begin
      Delete (L, Cu);
      Insert (L, E, Cu, I);
      pragma Assert (I);
      pragma Assert (Elements (L) = Old_K);
   end Nearly_Identity;

   procedure My_Include (L : in out Set; E : Element_Type) is
   begin
      if Contains (L, E) then
         Replace (L, E);
      else
         Insert (L, E);
      end if;
   end My_Include;

end P;
