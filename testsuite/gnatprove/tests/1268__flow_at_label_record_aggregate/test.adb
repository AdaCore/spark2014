pragma Extensions_Allowed (All_Extensions);

procedure Test with SPARK_Mode is
   type Rec is record
      Value : Integer;
   end record;

   X : Integer := 1;
begin
   <<L>>
   X := 2;

   declare
      Snapshot : constant Rec := (Value => X'At (L));
   begin
      pragma Assert (Snapshot.Value = 1);
   end;
end Test;
