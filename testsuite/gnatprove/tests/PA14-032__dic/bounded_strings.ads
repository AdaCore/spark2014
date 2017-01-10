pragma SPARK_Mode(On);

package Bounded_Strings is

   Maximum_Bound : constant := 2**16;
   subtype Index_Type is Positive range 1 .. Maximum_Bound;
   subtype Length_Type is Natural range 0 .. Maximum_Bound;

   type Bounded_String(Bound : Index_Type) is private --@DEFAULT_INITIAL_CONDITION:PASS
     with Default_Initial_Condition => Length(Bounded_String) = 0;

   -- Returns the number of characters stored in this bounded string.
   function Length(Source : Bounded_String) return Length_Type
     with
       Global => null,
         Inline;

   -- Returns a bounded string with the given upper bound and set to the initializer character.
   function Make(Upper_Bound : Index_Type; Initializer : Character) return Bounded_String
     with
       Global => null,
       Post => Make'Result.Bound = Upper_Bound and Length(Make'Result) = 1;


private

   type Bounded_String(Bound : Index_Type) is
      record
         Text : String(1 .. Bound) := (others => ' ');
         Length : Length_Type := 0;
      end record;

   function Length(Source : Bounded_String) return Length_Type is
     (Source.Length);

end Bounded_Strings;
