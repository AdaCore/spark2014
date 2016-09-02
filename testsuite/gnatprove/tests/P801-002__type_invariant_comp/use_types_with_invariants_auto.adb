package body Use_Types_With_Invariants_Auto with SPARK_Mode is

   procedure Set (C : in out Container; I : Positive; E : My_Integer) is
   begin
      C.Content (I) := E;
   end Set;

   procedure Set (C : in out Container_Bad; I : Positive; E : My_Integer_Bad)
   is
   begin
      C.Content (I) := E;
   end Set;

   procedure Test (I : Positive; E : My_Integer; F : My_Integer_Bad) is
   begin
      pragma Assert (From_Integer (To_Integer (E)) = E);
      pragma Assert (To_Integer (My_Integer'(From_Integer (I))) = I);

      --  These are not provable because the bodies are not in SPARK.
      pragma Assert (From_Integer (To_Integer (F)) = F); --@ASSERT:FAIL @PRECONDITION:FAIL
      pragma Assert (To_Integer (My_Integer_Bad'(From_Integer (I))) = I); --@ASSERT:FAIL
   end;

end Use_Types_With_Invariants_Auto;
