generic
   type Elem_Type is private;
   Null_Elem : Elem_Type;
   Max       : Positive;
package Bounded_Table
with Abstract_State => null
is
   pragma Annotate (GNATprove, Terminating, Bounded_Table);

   type Cursor_Type is private;

   type T is private
   with Iterable => (First       => First,
                     Next        => Next,
                     Has_Element => Has_Element,
                     Element     => Element);

   type Model_Type is array (Natural range <>) of Elem_Type
   with Ghost;

   function Model (Table : T) return Model_Type
   with Ghost;

   function Empty_Table return T
   with Post => Model (Empty_Table'Result)'Length = 0;

   function Length (Table : T) return Natural
   with Post => Length'Result = Model (Table)'Length;

   function Full (Table : T) return Boolean
   is (Length (Table) = Max);

   function First (Table : T) return Cursor_Type;

   function Has_Element (Table : T; Cursor : Cursor_Type) return Boolean;

   function Next (Table : T; Cursor : Cursor_Type) return Cursor_Type
   with Pre => Has_Element (Table, Cursor),
        Post => (if Has_Element (Table, Next'Result) then
                   Index_Of (Next'Result) > Index_Of (Cursor));

   function Element (Table : T; Cursor : Cursor_Type) return Elem_Type
   with Pre => Has_Element (Table, Cursor);

   function Member (Table : T; Elem : Elem_Type) return Boolean
   with Post => Member'Result = (for some E of Table => E = Elem);
   pragma Annotate (GNATprove, Iterable_For_Proof, "Contains", Member);

   procedure Push
     (Table : in out T;
      Elem  :        Elem_Type)
   with
     Pre  => Length (Table) < Max,
     Post => Length (Table) = Length (Table'Old) + 1 and then
             Member (Table, Elem) and then
             --  more generally:
             (for all E of Table'Old => Member (Table, E)) and then
             (for all E of Table => E = Elem or Member (Table'Old, E));

   function Index_Of (Cursor : Cursor_Type) return Natural;

private

   subtype Opt_Index_Type is Natural range 0 .. Max;
   subtype Index_Type is Opt_Index_Type range 1 .. Opt_Index_Type (Max);

   subtype Index_With_Sentinel is Natural range 1 .. Opt_Index_Type (Max) + 1;
   type Cursor_Type is new Index_With_Sentinel;
   function Index_Of (Cursor : Cursor_Type) return Natural is (Natural(Cursor));

   type Elem_Array is array (Index_Type) of Elem_Type;

   type T is record
      Elems : Elem_Array;
      Last  : Opt_Index_Type;
   end record;

end Bounded_Table;
