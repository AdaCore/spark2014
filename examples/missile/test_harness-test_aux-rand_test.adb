separate(Test_Harness.Test_Aux)
procedure Rand_Test(S : in Random.value) is
   package Val_Io is new Ada.Text_Io.Integer_Io(Random.Value);

   R : Random.Number;
   V : Random.Value;
begin
   Test.Section("Random test with seed = " &
                Random.value'Image(S));
   R := Random.Seed(s);
   for I in Integer range 1..20 loop
      Random.Get(N => R,
                 V => V);
      Val_Io.Put(V);
      Ada.Text_Io.Put_Line(" ");
   end loop;
end Rand_Test;
