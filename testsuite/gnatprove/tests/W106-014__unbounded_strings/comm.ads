with Ada.Strings.Maps;
with Ada.Strings.Unbounded;             use Ada.Strings.Unbounded;


package Comm with SPARK_Mode is

   package Unbounded_Strings_Subprograms is
      function To_Unbounded_String
        (Source : String)  return Unbounded_String
      with
        Post   =>
          Length (To_Unbounded_String'Result) = Source'Length
            and then
          (for all J in 1 .. Source'Length =>
             (Source (Source'First - 1 + J)
              = Element (To_Unbounded_String'Result, J))),
        Global => null;

      function Index
        (Source  : Unbounded_String;
         Pattern : String;
         Going   : Ada.Strings.Direction := Ada.Strings.Forward;
         Mapping : Ada.Strings.Maps.Character_Mapping := Ada.Strings.Maps.Identity) return Natural
      with
        Pre    => Pattern'Length /= 0,
        Post   => Index'Result in 1 .. Length (Source) - Pattern'Length + 1,
        Global => null;

      function Index
        (Source  : Unbounded_String;
         Pattern : String;
         From    : Positive;
         Going   : Ada.Strings.Direction := Ada.Strings.Forward;
         Mapping : Ada.Strings.Maps.Character_Mapping := Ada.Strings.Maps.Identity) return Natural
      with
        Pre    =>
          (if Length (Source) /= 0
           then From <= Length (Source))
             and then Pattern'Length /= 0,
        Post   => Index'Result in 0 |
                                  From .. Length (Source) - Pattern'Length + 1,
        Global => null;

      function Slice
        (Source : Unbounded_String;
         Low    : Positive;
         High   : Natural) return String
      with
        Pre    => Low - 1 <= Length (Source) and then High <= Length (Source),
        Post   =>
          Slice'Result'Length = Natural'Max (0, High - Low + 1)
            and then Slice'Result'First = 1
            and then (for all J in Slice'Result'Range =>
                        (Element (Source, Low - 1 + J) = Slice'Result (J))),
        Global => null;
   private
      pragma SPARK_Mode (Off);

      function To_Unbounded_String
        (Source : String)  return Unbounded_String
         renames Ada.Strings.Unbounded.To_Unbounded_String;

      function Index
        (Source  : Unbounded_String;
         Pattern : String;
         Going   : Ada.Strings.Direction := Ada.Strings.Forward;
         Mapping : Ada.Strings.Maps.Character_Mapping := Ada.Strings.Maps.Identity) return Natural
         renames Ada.Strings.Unbounded.Index;

      function Index
        (Source  : Unbounded_String;
         Pattern : String;
         From    : Positive;
         Going   : Ada.Strings.Direction := Ada.Strings.Forward;
         Mapping : Ada.Strings.Maps.Character_Mapping := Ada.Strings.Maps.Identity) return Natural
         renames Ada.Strings.Unbounded.Index;

      function Slice
        (Source : Unbounded_String;
         Low    : Positive;
         High   : Natural) return String
         renames Ada.Strings.Unbounded.Slice;
   end Unbounded_Strings_Subprograms;
end Comm;
