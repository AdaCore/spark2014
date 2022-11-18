with SPARK.Containers.Functional.Maps;

procedure Test_Maps is
   package My_Maps is new SPARK.Containers.Functional.Maps (String, Integer);
   use My_Maps;

   M : My_Maps.Map;
begin
   M := Add (M, (1 => 'a'), 1);

   pragma Assert (Has_Key (M, (15 => 'a')));

   --  SPARK can prove that Program_Error is never raised, so the code
   --  below should not be executable.

   if (for all X of M => X'First /= 15) then
      raise Program_Error;
   end if;
end Test_Maps;
