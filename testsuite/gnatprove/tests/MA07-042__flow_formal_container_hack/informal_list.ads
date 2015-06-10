with Ada.Strings;

package Informal_List with SPARK_Mode
is
   pragma Annotate (GNATprove, External_Axiomatization);

   type T is private;

   type U is new Ada.Strings.Alignment;

private
   pragma SPARK_Mode (Off);

   type T is new Ada.Strings.Alignment;

end Informal_List;
