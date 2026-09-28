pragma Extensions_Allowed (All_Extensions);
pragma Assertion_Policy (Check);
pragma SPARK_Mode;

with Gen;

procedure Main is
   --  Structural instantiation: the generic is referenced directly with
   --  actual parameters, without using 'new'.  The compiler implicitly
   --  creates a single shared instance per partition.
   package Int_Pair renames Gen (Integer);
   package Float_Pair renames Gen (Float);
   P : Int_Pair.Pair;
begin
   P := Int_Pair.Make (10, 20);
   pragma Assert (Int_Pair.Get_First (P) = 10);
   pragma Assert (Int_Pair.Get_Second (P) = 20);
end Main;
