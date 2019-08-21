private with Ada.Strings.Unbounded;

package Foo with
  SPARK_Mode
is
   type Unbounded_String is private;

   function To_String (Source : Unbounded_String) return String;

   function Length (Source : Unbounded_String) return Natural;

private
   package ASU renames Ada.Strings.Unbounded;

   type Unbounded_String is record
     Str : ASU.Unbounded_String;
   end record;

   function To_String (Source : Unbounded_String) return String is
     (ASU.To_String (Source.Str));

   function Length (Source : Unbounded_String) return Natural is
     (ASU.Length (Source.Str));

end Foo;
