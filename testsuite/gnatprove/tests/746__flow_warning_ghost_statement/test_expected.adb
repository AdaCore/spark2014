procedure Test_Expected with SPARK_Mode is
   G : Integer;

   procedure Do_Nothing with
     Global => (Proof_In => G),
     Post => True,
     Ghost;
   procedure Do_Nothing is
   begin
      pragma Assert (G > 0);
   end Do_Nothing;

   procedure P2 (B : Boolean) with Pre => B, Exceptional_Cases => (Program_Error => True);

   procedure P2 (B : Boolean) is
   begin
      if B then
         G := 12;
         return;
      end if;
      Do_Nothing;
      raise Program_Error;
   end P2;
begin
   null;
end Test_Expected;
