package body Types_With_Invariants with SPARK_Mode is

   procedure Set (C : in out Container; I : Positive; E : My_Integer) is
   begin
      C.Content (I) := E;
   end Set;

   procedure Internal_Test (I : Positive; E : My_Integer) with
     Ghost,
     Pre => True
   is
      subtype Int is My_Integer;
      T : Int := E;
   begin
      pragma Assert (My_Integer (T).Val = E.Val);
      pragma Assert (if E.Val /= 0 or else E.Sign then
                        From_Integer (To_Integer (E)) = E);
      pragma Assert (To_Integer (My_Integer'(From_Integer (I))) = I);
      --  These is not provable because Internal_Test is internal and thus E
      --  is not required to fulfill its invariant.
      pragma Assert (From_Integer (To_Integer (E)) = E); --@ASSERT:FAIL
   end Internal_Test;

   procedure Test (I : Positive; E : My_Integer) is
   begin
      pragma Assert (From_Integer (To_Integer (E)) = E);
      pragma Assert (To_Integer (My_Integer'(From_Integer (I))) = I);
      Internal_Test (I, E);
   end;

end Types_With_Invariants;
