with Ada.Strings;

package Informal_List
is
   pragma Annotate (GNATprove, External_Axiomatization);

   type T is private;

   type U is new Ada.Strings.Alignment;

private

   type T is new Ada.Strings.Alignment;

end Informal_List;
