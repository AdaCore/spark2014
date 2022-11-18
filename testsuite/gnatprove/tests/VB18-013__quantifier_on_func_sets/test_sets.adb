with SPARK.Containers.Functional.Sets;

procedure Test_Sets is
   package My_Sets is new SPARK.Containers.Functional.Sets (String);
   use My_Sets;

   S : My_Sets.Set;
begin
   S := Add (S, (1 => 'a'));

   pragma Assert (Contains (S, (15 => 'a')));

   --  SPARK can prove that Program_Error is never raised, so the code
   --  below should not be executable.

   if (for all X of S => X'First /= 15) then
      raise Program_Error;
   end if;
end Test_Sets;
