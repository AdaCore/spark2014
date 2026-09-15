pragma Extensions_Allowed (All_Extensions);

procedure Record_Snapshot
  (A1, A2 : Integer;
   X1, X2 : Boolean;
   O1     : out Integer;
   O2     : out Boolean)
with SPARK_Mode
is
   type Rec is record
      A : Integer;
      X : Boolean;
   end record;

   function Pick_A (R : Rec) return Integer is (R.A);

   function Pick_X (R : Rec) return Boolean is (R.X);

   Obj : Rec := (A => A1, X => X1);
begin
   goto Capture;

   <<Capture>>
   Obj.A := A2;
   Obj.X := X2;

   O1 := Pick_A (Obj'At (Capture));
   O2 := Pick_X (Obj'At (Capture));
end Record_Snapshot;
