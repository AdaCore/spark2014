procedure Test (Choice : Positive) with SPARK_Mode, Pre => Choice <= 3 is
   type Rec is record
      F, G : Integer;
   end record;
   type Arr is array (Positive range <>) of Rec;
   X : Rec with Relaxed_Initialization;
   Tail : Arr (1 .. 1) := (others => (F => 1, G => 2));
   Result : Arr (1 .. 2) with Relaxed_Initialization;
begin
   X.F := 3;
   case Choice is
      when 1 =>
         Result := X & Tail;
         pragma Assert (Result (1).F = 3); -- @ASSERT:PASS
         pragma Assert (Result (2).F = 1); -- @ASSERT:PASS
         pragma Assert (Result (1).G'Initialized); -- @ASSERT:FAIL
      when 2 =>
         Result := Tail & X;
         pragma Assert (Result (1).F = 1); -- @ASSERT:PASS
         pragma Assert (Result (2).F = 3); -- @ASSERT:PASS
         pragma Assert (Result (2).G'Initialized); -- @ASSERT:FAIL
      when others =>
         Result := X & Tail (1);
         pragma Assert (Result (1).F = 3); -- @ASSERT:PASS
         pragma Assert (Result (2).F = 1); -- @ASSERT:PASS
         pragma Assert (Result (1).G'Initialized); -- @ASSERT:FAIL
   end case;
end Test;
