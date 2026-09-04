pragma Extensions_Allowed (All_Extensions);

procedure Test (A1, A2 : Integer; O : out Integer)
with
  SPARK_Mode,
  Depends => (O => A1, null => A2)
is
   type R is record
      A : Integer;
   end record;

   Obj : R := (A => A1);
begin
   <<Init>>
   Obj.A := A2;

   declare
      Saved : constant R := Obj'At (Init);
   begin
      O := Saved.A;
   end;
end;
