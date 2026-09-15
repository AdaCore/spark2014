pragma Extensions_Allowed (All_Extensions);

procedure Test
  (A1, A2 : Integer;
   X1, X2 : Boolean;
   O1     : out Integer;
   O2, O3 : out Boolean)
with
  SPARK_Mode,
  Depends => ((O1, O2) => (A1, X1), O3 => null, null => (A2, X2))
is
   type Empty_Record is null record;

   type Rec is record
      A : Integer;
      X : Boolean;
   end record;

   procedure Pick (R : Rec; A : out Integer; X : out Boolean)
   with Depends => ((A, X) => R)
   is
   begin
      A := R.A;
      X := R.X;
   end Pick;

   procedure Pick_Empty (R : Empty_Record; O : out Boolean)
   with Depends => (O => null, null => R)
   is
      pragma Unreferenced (R);
   begin
      O := True;
   end Pick_Empty;

   Obj     : Rec := (A => A1, X => X1);
   Nothing : Empty_Record;
begin
   <<Init>>
   Obj.A := A2;
   Obj.X := X2;

   Pick (Obj'At (Init), O1, O2);
   Pick_Empty (Nothing'At (Init), O3);
end;
