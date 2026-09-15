pragma Extensions_Allowed (All_Extensions);

procedure Test
  (A1, A2, X1, X2 : Boolean;
   O1, O2         : out Boolean)
with
  SPARK_Mode,
  Depends => ((O1, O2) => (A1, A2, X1, X2))
is
   type Rec is record
      A : Boolean;
      X : Boolean;
   end record;

   function Pick_A (R : Rec) return Boolean is (R.A);

   function Pick_X (R : Rec) return Boolean is (R.X);

   Obj : Rec := (A => A1, X => X1);
begin
   O1 := False;
   O2 := False;

   for Iteration in 1 .. 2 loop
      if Iteration = 2 then
         Obj := (A => A2, X => X2);
      end if;

      <<Capture>>
      Obj := (A => False, X => False);

      O1 := O1 xor Pick_A (Obj'At (Capture));
      O2 := O2 xor Pick_X (Obj'At (Capture));
      pragma Loop_Invariant (Iteration in 1 .. 2);
   end loop;
end;
