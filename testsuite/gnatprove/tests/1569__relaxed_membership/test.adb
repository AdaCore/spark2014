procedure Test (Choice : Positive; Result : out Boolean) with
  SPARK_Mode, Pre => Choice <= 6
is
   type I is new Integer with Relaxed_Initialization;
   type Rec is record
      F : I;
   end record;
   type Arr is array (1 .. 1) of I;
   A : Rec := (F => 0);
   C : Rec := (F => 1);
   B : Rec;
   AA : Arr := (others => 0);
   CC : Arr := (others => 1);
   BB : Arr;
begin
   case Choice is
      when 1 =>
         Result := A in C | B; -- @INIT_BY_PROOF:FAIL
      when 2 =>
         Result := AA in CC | BB; -- @INIT_BY_PROOF:FAIL
      when 3 =>
         Result := AA not in CC | BB; -- @INIT_BY_PROOF:FAIL
      when 4 =>
         Result := AA in AA | BB; -- @INIT_BY_PROOF:PASS
         pragma Assert (Result); -- @ASSERT:PASS
      when 5 =>
         BB := (others => 0);
         Result := AA in CC | BB; -- @INIT_BY_PROOF:PASS
         pragma Assert (Result); -- @ASSERT:PASS
      when others =>
         Result := A in C | A; -- @INIT_BY_PROOF:PASS
         pragma Assert (Result); -- @ASSERT:PASS
   end case;
end Test;
