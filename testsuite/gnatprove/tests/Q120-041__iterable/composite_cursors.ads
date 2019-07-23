package Composite_Cursors with SPARK_Mode is
   type Nat_Array is array (Positive range <>) of Natural;

   type Array_Cursor is array (Integer range 1 .. 1) of Natural;

   type Cont1 is record
      Content : Nat_Array (1 .. 100);
      Length  : Natural;
   end record
     with Iterable =>
       (First       => First,
        Next        => Next,
        Has_Element => Has_Element,
        Element     => Element),
     Predicate => Length <= 100;

   function First (C : Cont1) return Array_Cursor is
      (1 => 1);

   function Next (C : Cont1; P : Array_Cursor) return Array_Cursor is
     (1 => P (1) + 1)
   with Pre => Has_Element (C, P);

   function Has_Element (C : Cont1; P : Array_Cursor) return Boolean is
      (P (1) in 1 .. C.Length);

   function Element (C : Cont1; P : Array_Cursor) return Natural is
      (C.Content (P (1)))
   with Pre => Has_Element (C, P);

   type Rec_Cursor is record
      Content : Natural;
   end record;

   type Cont2 is record
      Content : Nat_Array (1 .. 100);
      Length  : Natural;
   end record
     with Iterable =>
       (First       => First,
        Next        => Next,
        Has_Element => Has_Element,
        Element     => Element),
     Predicate => Length <= 100;

   function First (C : Cont2) return Rec_Cursor is
      (Content => 1);

   function Next (C : Cont2; P : Rec_Cursor) return Rec_Cursor is
     (Content => P.Content + 1)
   with Pre => Has_Element (C, P);

   function Has_Element (C : Cont2; P : Rec_Cursor) return Boolean is
      (P.Content in 1 .. C.Length);

   function Element (C : Cont2; P : Rec_Cursor) return Natural is
      (C.Content (P.Content))
   with Pre => Has_Element (C, P);
end Composite_Cursors;
