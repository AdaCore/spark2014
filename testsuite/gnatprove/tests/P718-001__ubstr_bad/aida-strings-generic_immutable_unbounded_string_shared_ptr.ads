with SPARK.Containers.Formal.Vectors;
with Aida.Strings.Generic_Immutable_Unbounded_String;
with Aida.Generic_Shared_Ptr;
with Ada.Containers; use Ada.Containers;

generic
   Capacity : Ada.Containers.Count_Type;
package Aida.Strings.Generic_Immutable_Unbounded_String_Shared_Ptr with SPARK_Mode is

   use type Ada.Containers.Count_Type;

   type T is private with Default_Initial_Condition => Length (T) = 0;

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
   pragma SPARK_Mode (Off);

   package US renames Aida.Strings.Generic_Immutable_Unbounded_String;

   type US_Ptr is access US.T;

   package Smart_Pointers is new Aida.Generic_Shared_Ptr (T => US.T,
                                                          P => US_Ptr);

   type T is
      record
         SP : Smart_Pointers.Pointer := Smart_Pointers.Create (new US.T);
      end record;

   function Length (This : T) return Ada.Containers.Count_Type is (US.Length (Smart_Pointers.Value (This.SP).all));

   function Char_At (This  : T;
                     Index : Positive) return Character is (US.Char_At (Smart_Pointers.Value (This.SP).all, Index));

   function To_String (This : T) return String is (US.To_String (Smart_Pointers.Value (This.SP).all));

end Aida.Strings.Generic_Immutable_Unbounded_String_Shared_Ptr;
