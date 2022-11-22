with SPARK.Containers.Functional.Maps;
with SPARK.Containers.Functional.Sets;

procedure Main
  with
    SPARK_Mode => On
is

   procedure Test_Maps is
      package My_Maps is new SPARK.Containers.Functional.Maps (String, Integer);
      use My_Maps;

      M : My_Maps.Map;
   begin
      M := Add (M, (1 => 'a'), 1);

      pragma Assert (Has_Key (M, (15 => 'a')));

      --  SPARK can prove that Program_Error is never raised, so the code
      --  below should not be executable.

      pragma Assert (for some X of M => X'First = 15);
   end Test_Maps;

   procedure Test_Sets is
      package My_Sets is new SPARK.Containers.Functional.Sets (String);
      use My_Sets;

      S : My_Sets.Set;
   begin
      S := Add (S, (1 => 'a'));

      pragma Assert (Contains (S, (15 => 'a')));

      --  SPARK can prove that Program_Error is never raised, so the code
      --  below should not be executable.

      pragma Assert (for some X of S => X'First = 15);
   end Test_Sets;

begin
   Test_Maps;
   Test_Sets;
end Main;
