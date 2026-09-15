pragma Extensions_Allowed (All_Extensions);

procedure Test
  (A                : in out String;
   V                :        Character;
   O_Call, O_Assign :    out Character)
with
  SPARK_Mode,
  Pre     => A'Length > 0,
  Depends => (A =>+ V, (O_Call, O_Assign) => A)
is
   function Head (S : String) return Character
   with
     Global  => null,
     Pre     => S'Length > 0,
     Depends => (Head'Result => S);

   function Head (S : String) return Character is
   begin
      return S (S'First);
   end Head;

   Saved : String (A'Range);
begin
   <<Capture>>
   A (A'First) := V;
   O_Call := Head (A'At (Capture));
   Saved := A'At (Capture);
   O_Assign := Saved (Saved'First);
end Test;
