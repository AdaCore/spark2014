pragma Warnings (Off, "function contract not available for proof");
pragma Warnings (Off, "no Global contract available");

with Ada.Strings.Bounded;
with Ada.Strings.Bounded.Hash;
with Ada.Containers.Formal_Hashed_Maps;
with SB; use SB;

package Test with SPARK_Mode is

   function SBHash is new Ada.Strings.Bounded.Hash(SB);

   type Scale is new Integer;
   package Scales_Map is
	new Ada.Containers.Formal_Hashed_Maps(Key_Type =>
		SB.Bounded_String,
		Element_Type => Scale,
		Hash => SBHash,
		Equivalent_Keys => SB."=" );

   Repository : Scales_Map.Map := Scales_Map.Empty_Map;
end Test;
