pragma Extensions_Allowed (All_Extensions);

procedure Test
  (First_1, First_2   :     Boolean;
   Second_1, Second_2 :     Boolean;
   O1, O2             : out Boolean)
with
  SPARK_Mode,
  Depends => ((O1, O2) => (First_1, First_2, Second_1, Second_2))
is
   type Arr is array (1 .. 2) of Boolean;

   A : Arr := (First_1, First_2);
begin
   O1 := False;
   O2 := False;

   for Iteration in 1 .. 2 loop
      if Iteration = 2 then
         A := (Second_1, Second_2);
      end if;

      <<Capture>>
      A := (False, False);

      O1 := O1 xor A'At (Capture) (1);
      O2 := O2 xor A'At (Capture) (2);
      pragma Loop_Invariant (Iteration in 1 .. 2);
   end loop;
end Test;
