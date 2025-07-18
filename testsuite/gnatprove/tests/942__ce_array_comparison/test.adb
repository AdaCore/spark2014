procedure Test with Spark_Mode is
   procedure Test_Lt (B : Boolean) is
      procedure Test_Early_Exit (X, Y : out String) with
        Pre => X'Length <= 4
        and then Y'Length <= 4;
      procedure Test_Early_Exit (X, Y : out String) is
      begin
         X := (others => 'o');
         Y := (others => 'o');
         if X'Length = Y'Length then
            pragma Assert (X < Y); -- @ASSERT:FAIL @COUNTEREXAMPLE
         elsif B then
            pragma Assert (X < Y); -- @ASSERT:FAIL @COUNTEREXAMPLE
         else
            pragma Assert (not (X < Y)); -- @ASSERT:FAIL @COUNTEREXAMPLE
         end if;
      end Test_Early_Exit;

      procedure Test_Element_Comparison  (X, Y : String) with
        Pre => X'Length = 4
        and then Y'Length = 4;

      procedure Test_Element_Comparison  (X, Y : String) is
      begin
         if X (X'First) = Y (Y'First) then
            if B then
               pragma Assert (X < Y); -- @ASSERT:FAIL @COUNTEREXAMPLE
            else
               pragma Assert (not (X < Y)); -- @ASSERT:FAIL @COUNTEREXAMPLE
            end if;
         else
            if B then
               pragma Assert (X < Y); -- @ASSERT:FAIL @COUNTEREXAMPLE
            else
               pragma Assert (not (X < Y)); -- @ASSERT:FAIL @COUNTEREXAMPLE
            end if;
         end if;
      end Test_Element_Comparison;
   begin
      null;
   end Test_Lt;

   procedure Test_Gt (B : Boolean) is
      procedure Test_Early_Exit (X, Y : out String) with
        Pre => X'Length <= 4
        and then Y'Length <= 4;
      procedure Test_Early_Exit (X, Y : out String) is
      begin
         X := (others => 'o');
         Y := (others => 'o');
         if X'Length = Y'Length then
            pragma Assert (X > Y); -- @ASSERT:FAIL @COUNTEREXAMPLE
         elsif B then
            pragma Assert (X > Y); -- @ASSERT:FAIL @COUNTEREXAMPLE
         else
            pragma Assert (not (X > Y)); -- @ASSERT:FAIL @COUNTEREXAMPLE
         end if;
      end Test_Early_Exit;

      procedure Test_Element_Comparison  (X, Y : String) with
        Pre => X'Length = 4
        and then Y'Length = 4;

      procedure Test_Element_Comparison  (X, Y : String) is
      begin
         if X (X'First) = Y (Y'First) then
            if B then
               pragma Assert (X > Y); -- @ASSERT:FAIL @COUNTEREXAMPLE
            else
               pragma Assert (not (X > Y)); -- @ASSERT:FAIL @COUNTEREXAMPLE
            end if;
         else
            if B then
               pragma Assert (X > Y); -- @ASSERT:FAIL @COUNTEREXAMPLE
            else
               pragma Assert (not (X > Y)); -- @ASSERT:FAIL @COUNTEREXAMPLE
            end if;
         end if;
      end Test_Element_Comparison;
   begin
      null;
   end Test_Gt;

   procedure Test_Le (B : Boolean) is
      procedure Test_Early_Exit (X, Y : out String) with
        Pre => X'Length <= 4
        and then Y'Length <= 4;
      procedure Test_Early_Exit (X, Y : out String) is
      begin
         X := (others => 'o');
         Y := (others => 'o');
         if X'Length = Y'Length then
            pragma Assert (not (X <= Y)); -- @ASSERT:FAIL @COUNTEREXAMPLE
         elsif B then
            pragma Assert (X <= Y); -- @ASSERT:FAIL @COUNTEREXAMPLE
         else
            pragma Assert (not (X <= Y)); -- @ASSERT:FAIL @COUNTEREXAMPLE
         end if;
      end Test_Early_Exit;

      procedure Test_Element_Comparison  (X, Y : String) with
        Pre => X'Length = 4
        and then Y'Length = 4;

      procedure Test_Element_Comparison  (X, Y : String) is
      begin
         if X (X'First) = Y (Y'First) then
            if B then
               pragma Assert (X <= Y); -- @ASSERT:FAIL @COUNTEREXAMPLE
            else
               pragma Assert (not (X <= Y)); -- @ASSERT:FAIL @COUNTEREXAMPLE
            end if;
         else
            if B then
               pragma Assert (X <= Y); -- @ASSERT:FAIL @COUNTEREXAMPLE
            else
               pragma Assert (not (X <= Y)); -- @ASSERT:FAIL @COUNTEREXAMPLE
            end if;
         end if;
      end Test_Element_Comparison;
   begin
      null;
   end Test_Le;

   procedure Test_Ge (B : Boolean) is
      procedure Test_Early_Exit (X, Y : out String) with
        Pre => X'Length <= 4
        and then Y'Length <= 4;
      procedure Test_Early_Exit (X, Y : out String) is
      begin
         X := (others => 'o');
         Y := (others => 'o');
         if X'Length = Y'Length then
            pragma Assert (not (X >= Y)); -- @ASSERT:FAIL @COUNTEREXAMPLE
         elsif B then
            pragma Assert (X >= Y); -- @ASSERT:FAIL @COUNTEREXAMPLE
         else
            pragma Assert (not (X >= Y)); -- @ASSERT:FAIL @COUNTEREXAMPLE
         end if;
      end Test_Early_Exit;

      procedure Test_Element_Comparison  (X, Y : String) with
        Pre => X'Length = 4
        and then Y'Length = 4;

      procedure Test_Element_Comparison  (X, Y : String) is
      begin
         if X (X'First) = Y (Y'First) then
            if B then
               pragma Assert (X >= Y); -- @ASSERT:FAIL @COUNTEREXAMPLE
            else
               pragma Assert (not (X >= Y)); -- @ASSERT:FAIL @COUNTEREXAMPLE
            end if;
         else
            if B then
               pragma Assert (X >= Y); -- @ASSERT:FAIL @COUNTEREXAMPLE
            else
               pragma Assert (not (X >= Y)); -- @ASSERT:FAIL @COUNTEREXAMPLE
            end if;
         end if;
      end Test_Element_Comparison;
   begin
      null;
   end Test_Ge;

begin
   null;
end;
