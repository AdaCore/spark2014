pragma Extensions_Allowed (All_Extensions);

procedure Test_Scalar (C1, C2 : Integer; O : out Integer) with
  SPARK_Mode,
  Depends => (O => (C1, C2))
is
   X : Integer := C1;
begin
   <<Init>>
   X := C2;

   declare
      C : constant Integer := X;

      subtype S is Integer range X'At (Init) .. C; --  This should be rejected, X'At (Init) is a variable input

      function Add return Integer;
      --   with
      --    Global => (??, C);

      function Add return Integer is (S'First + S'Last);
   begin
      O := Add;
   end;
end Test_Scalar;
