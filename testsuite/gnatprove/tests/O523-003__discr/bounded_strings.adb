pragma Spark_Mode(On);

with Ada.Characters.Latin_1;

package body Bounded_Strings is

   function Make(Upper_Bound : Index_Type; Initializer : String) return Bounded_String is
      B : Bounded_String(Upper_Bound);
   begin
      B.Text := (others => Ada.Characters.Latin_1.Nul);
      B.Text(1 .. Initializer'Length) := Initializer;
      B.Size := Initializer'Length;
      return B;
   end Make;

end Bounded_Strings;
