pragma Extensions_Allowed (All_Extensions);

procedure Test (Input : Integer; Output : out Integer) with
  Depends => (Output => Input)
is
   type Source_Rec is record
      DS : Integer;
   end record;

   type Target_Rec (DT : Integer) is null record;

   Source : constant Source_Rec := (DS => Input);
begin
   <<Save>>
   declare
      Object : Target_Rec (DT => Source.DS'At (Save));
   begin
      Output := Object.DT;
   end;
end Test;
