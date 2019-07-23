package body Bounded_Table
is

   function Element (Table : T; Cursor : Cursor_Type) return Elem_Type
   is (Table.Elems (Index_Type (Cursor)));

   -----------------------------------------------------------------------------

   function Empty_Table return T
   is (T'(Elems => (others => Null_Elem),
          Last  => 0));

   -----------------------------------------------------------------------------

   function First (Table : T) return Cursor_Type
   with Refined_Post => First'Result = Cursor_Type'First
   is
      pragma Unreferenced (Table);
   begin
      return Cursor_Type'First;
   end First;

   -----------------------------------------------------------------------------

   function Has_Element (Table : T; Cursor : Cursor_Type) return Boolean
   is (Cursor < Cursor_Type'Last and then Opt_Index_Type (Cursor) <= Table.Last);

   -----------------------------------------------------------------------------

   function Length (Table : T) return Natural
   is (Natural (Table.Last));

   -----------------------------------------------------------------------------

   function Member (Table : T; Elem : Elem_Type) return Boolean
   is (for some I in Table.Elems'First .. Table.Last =>
       Table.Elems (I) = Elem);

   -----------------------------------------------------------------------------

   function Model (Table : T) return Model_Type
   is (Model_Type (Table.Elems (Table.Elems'First .. Table.Last)));

   -----------------------------------------------------------------------------

   function Next (Table : T; Cursor : Cursor_Type) return Cursor_Type
   is (Cursor + 1)
   with Refined_Post => Next'Result > Cursor;

   -----------------------------------------------------------------------------

   procedure Push
     (Table : in out T;
      Elem  :        Elem_Type)
   is
   begin
      Table.Last               := Table.Last + 1;
      Table.Elems (Table.Last) := Elem;
   end Push;

end Bounded_Table;
