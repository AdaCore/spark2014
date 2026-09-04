pragma Extensions_Allowed (All_Extensions);

procedure Test with SPARK_Mode is
begin
   --  The snapshot definition is a flow-model write inside the loop. It must
   --  not become a source-object loop write.

   for Index in 1 .. 10 loop
      <<Capture>>
      null;
      pragma Assert (Index'At (Capture) = Index);
      pragma Loop_Invariant (Index in 1 .. 10);
   end loop;
end Test;
