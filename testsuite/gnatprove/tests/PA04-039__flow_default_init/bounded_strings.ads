pragma SPARK_Mode(On);

package Bounded_Strings is

   Maximum_Bound : constant := 2**16;
   subtype Index_Type is Positive range 1 .. Maximum_Bound;
   subtype Length_Type is Natural range 0 .. Maximum_Bound;

   type Bounded_String(Bound : Index_Type) is private
     with Default_Initial_Condition => Length(Bounded_String) = 0;
   --     Type_Invariant => Length(Bounded_String) <= Bound;
   -- SPARK does not (yet) support type invariants.

   -- Returns the number of characters stored in this bounded string.
   function Length(Source : Bounded_String) return Length_Type
     with
       Global => null,
       Inline;

   procedure Append(Target : in out Bounded_String; Item : in Character)
     with
       Global => null,
       Depends => (Target =>+ Item),
       Pre => Length(Target) + 1 <= Target.Bound,
       Post => Length(Target) = Length(Target)'Old + 1;

   -- Erases the contents of the given bounded string.
   procedure Clear(Target : out Bounded_String)
     with
       Global => null,
       Depends => (Target =>+ null),
       Post => Length(Target) = 0;

private

   type Bounded_String(Bound : Index_Type) is
      record
         Text : String(1 .. Bound) := (others => ' ');
         Length : Length_Type := 0;
      end record;

   function Length(Source : Bounded_String) return Length_Type is
     (Source.Length);

end Bounded_Strings;
