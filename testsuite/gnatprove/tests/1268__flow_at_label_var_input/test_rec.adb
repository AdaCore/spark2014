pragma Extensions_Allowed (All_Extensions);

procedure Test_Rec (C1, C2 : Integer; O : out Integer) with
  SPARK_Mode,
  Depends => (O => (C1, C2))
is
   type Rec is record
      A : Integer;
      B : Integer;
   end record;

   R : Rec := (A => C1, B => 0);
begin
   <<Init>>
   R.A := C2;

   declare
      C : constant Integer := R.A;

      subtype S is Integer range R'At (Init).A .. C; --  This should be rejected, X'At (Init) is a variable input

      function Add return Integer;
      --   with
      --    Global => (??, C);

      function Add return Integer is (S'First + S'Last);
   begin
      O := Add;
   end;
end Test_Rec;
