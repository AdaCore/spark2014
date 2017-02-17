pragma SPARK_Mode(On);

package Bounded_Strings is

   Maximum_Bound : constant := 2**16;
   subtype Index_Type is Positive range 1 .. Maximum_Bound;
   subtype Size_Type is Natural range 0 .. Maximum_Bound;

   type Bounded_String(Bound : Index_Type) is private;

   -- Returns the number of characters stored in this bounded string.
   function Size(B : Bounded_String) return Size_Type
     with Global => null;

   -- Returns a bounded string with the given upper bound and set to the initializer string.
   function Make(Upper_Bound : Index_Type; Initializer : String) return Bounded_String
     with
       Global => null,
       Pre => Initializer'Length <= Upper_Bound,
       Post => Size(Make'Result) = Initializer'Length;

private

   type Bounded_String(Bound : Index_Type) is
      record
         Text : String(1 .. Bound);
         Size : Size_Type;
      end record;

   function Size(B : Bounded_String) return Size_Type is
     (B.Size);

end Bounded_Strings;
