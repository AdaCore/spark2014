package Sums with SPARK_Mode is
   pragma Annotate (GNATprove, External_Axiomatization);

   subtype Extended_Index is Integer range 0 .. 2 ** 16;
   subtype Index is Integer range 1 .. Extended_Index'Last;

   subtype Vector_Element is
     Integer range Integer'First / Index'Last .. Integer'Last / Index'Last;

   type Vector is array (Index range <>) of Vector_Element;

   type Slice_Bounds is
      record
         Lo : Index;
         Hi : Extended_Index;
      end record;

   function Sum (X : Vector; Bounds : Slice_Bounds) return Integer with
     Pre => (Bounds.Lo > Bounds.Hi) or else
     (X'First <= Bounds.Lo and Bounds.Hi <= X'Last);

end Sums;
