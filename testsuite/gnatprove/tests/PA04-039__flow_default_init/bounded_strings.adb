pragma SPARK_Mode(On);

with Ada.Characters.Latin_1;

package body Bounded_Strings is

   procedure Append(Target : in out Bounded_String; Item : in Character) is
   begin
      Target.Text(Target.Length + 1) := Item;
      Target.Length := Target.Length + 1;
   end Append;


   procedure Clear(Target : out Bounded_String) is
   begin
      Target.Text := (others => Ada.Characters.Latin_1.Nul);
      Target.Length := 0;
   end Clear;

end Bounded_Strings;
