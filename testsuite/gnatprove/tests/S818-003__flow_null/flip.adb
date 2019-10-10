with P;

procedure Flip (X : in out Boolean) with Global => null is
begin
   X := not X;  --  dummy effect, to avoid any special-casing

   P.Dummy_With_Global;
   P.Dummy_With_Depends;
   P.Dummy_With_Global_And_Depends;

   P.Dummy_With_Global_And_Imported;
   P.Dummy_With_Depends_And_Imported;
   P.Dummy_With_Global_And_Depends_And_Imported;
end;
