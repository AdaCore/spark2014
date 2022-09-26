with SPARK.Containers.Formal.Unbounded_Vectors;
with Ada.Containers; use Ada.Containers;

package Aida.Strings.Generic_Immutable_Unbounded_String with SPARK_Mode is

   use type Ada.Containers.Count_Type;

   type T is limited private with Default_Initial_Condition => null;

   function Length (This : T) return Ada.Containers.Count_Type with
     Global => null;

   function Char_At (This  : T;
                     Index : Positive) return Character with
     Global => null,
     Pre => Length (This) > 0 and then Index <= Positive (Length (This));

   function To_String (This : T) return String with
     Pre    => Length (This) < MAX_LENGTH,
     Global => null;

private

   package Char_Vectors is new SPARK.Containers.Formal.Unbounded_Vectors
     (Index_Type   => Positive,
      Element_Type => Character);

   type T is limited
      record
         Text : Char_Vectors.Vector;
      end record;

end Aida.Strings.Generic_Immutable_Unbounded_String;
