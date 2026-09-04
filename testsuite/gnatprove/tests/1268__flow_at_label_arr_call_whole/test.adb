pragma Extensions_Allowed (All_Extensions);

procedure Test
  (Before_1, Before_2 :     Integer;
   After_1, After_2   :     Integer;
   O                  : out Integer)
with
  SPARK_Mode,
  Depends => (O => (Before_1, Before_2), null => (After_1, After_2))
is
   type Arr is array (1 .. 2) of Integer;

   function First (A : Arr) return Integer
   with Global => null, Depends => (First'Result => A);

   function First (A : Arr) return Integer is
   begin
      return A (1);
   end First;

   A : Arr := (Before_1, Before_2);
begin
   <<Capture>>
   A := (After_1, After_2);
   O := First (A'At (Capture));
end Test;
