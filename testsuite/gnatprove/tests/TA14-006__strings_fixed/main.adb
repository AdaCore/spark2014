with Ada.Strings.Fixed; use Ada.Strings.Fixed;
with Ada.Strings.Maps;
with Ada.Strings.Search;

procedure Main with SPARK_Mode
is
   T : String (1 .. 99);
   S : String (1 .. 101);
   Identity : constant Ada.Strings.Maps.Character_Mapping :=
     Ada.Strings.Maps.Identity;
   procedure Lemma_Index
     (Source  : String;
      Pattern : String;
      Mapping : Ada.Strings.Maps.Character_Mapping;
      Result  : Integer)
   with Ghost,
     Pre  => Pattern'Length /= 0
       and then Source'Length /= 0
       and then Result in Source'First .. (Source'Last - (Pattern'Length - 1))
       and then Ada.Strings.Search.Match (Source, Pattern, Mapping, Result)
       and then
         (for all K in Source'First .. Result - 1 =>
            not (Ada.Strings.Search.Match (Source, Pattern, Mapping, K))),
     Post => Index (Source, Pattern, Mapping => Mapping) = Result;
   procedure Lemma_Index
     (Source  : String;
      Pattern : String;
      Mapping : Ada.Strings.Maps.Character_Mapping;
      Result  : Integer)
   is null;
begin
   T := 11 * "123456789";
   pragma Assume (Ada.Strings.Search.Is_Identity (Identity));
   for K in 1 .. 8 loop
      pragma Assert (Ada.Strings.Maps.Value (Identity, T (K)) /= '9');
      pragma Assert (not (Ada.Strings.Search.Match (T, "91", Identity, K)));
      pragma Loop_Invariant
        (for all J in 1 .. K =>
           not (Ada.Strings.Search.Match (T, "91", Identity, J)));
   end loop;
   pragma Assert (for all K in 1 .. 8 =>
                    not (Ada.Strings.Search.Match (T, "91", Identity, K)));
   Lemma_Index (T, "91", Identity, 9);
   pragma Assert (Index (T, "91", Mapping => Identity) = 9);
   pragma Assert (Index (T, "92", Mapping => Identity) = 0);

   T := Overwrite (T, 18, "888");
   pragma Assert (T (17 .. 23) = "8888345");
   S := Overwrite (T, 93, "123456789");
   pragma Assert (S (91 .. 95) = "12123");
   pragma Assert (T (91 .. 95) = "12345");
   pragma Assert (S (1 .. 91) = T (1 .. 91));
   pragma Assert (S (94 .. 101) = "23456789");
   pragma Assert (T (92 .. 99) = "23456789");
   pragma Assert (S (94 .. 101) = T (92 .. 99));
   pragma Assert (S = Insert (T, 92, "21"));
   pragma Assert (T = Delete (S, 92, 93));
end Main;


