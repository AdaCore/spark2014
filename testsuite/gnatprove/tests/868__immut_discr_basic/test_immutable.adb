package body Test_Immutable is

   procedure P (I : Positive; X : T1) is
      Y1 : T1 := (False, False, others => <>);
      Y2 : T1 := (False, False, 222);
      Y3 : T1 := (Y2 with delta F => 333);
      Y4 : constant T1 := (True, True, 444);
      Y5 : T1 (True, False);
      Y6 : T2;
      Y7 : constant T1 := Y1'Update(F => 777);
      Y8 : T1 := Y4'Update(F => 888);
      Y9 : T1 := Y5'Update(F => 999);
      Z  : T2 := (True, False, 10101);
   begin
      --  All the objects here are constrained
      pragma Assert (Y1'Constrained); --@ASSERT:PASS
      pragma Assert (Y2'Constrained); --@ASSERT:PASS
      pragma Assert (Y3'Constrained); --@ASSERT:PASS
      pragma Assert (Y4'Constrained); --@ASSERT:PASS
      pragma Assert (Y5'Constrained); --@ASSERT:PASS
      pragma Assert (Y6'Constrained); --@ASSERT:PASS
      pragma Assert (Y7'Constrained); --@ASSERT:PASS
      pragma Assert (Y8'Constrained); --@ASSERT:PASS
      pragma Assert (Y9'Constrained); --@ASSERT:PASS

      --  The cases below could fail on the discriminant check
      case I is
         when 1 =>
            Y1 := X; -- @DISCRIMINANT_CHECK:FAIL

         when 2 =>
            Y2 := X; -- @DISCRIMINANT_CHECK:FAIL

         when 3 =>
            Y3 := X; -- @DISCRIMINANT_CHECK:FAIL

         when 4 =>
            --  Cannot assign to a constant
            null;

         when 5 =>
            Y5 := Z;
            pragma Assert (True); --@ASSERT:PASS
            Y5 := X; -- @DISCRIMINANT_CHECK:FAIL

         when 6 =>
            Y6 := Z;
            pragma Assert (True); --@ASSERT:PASS
            Y6 := X; -- @DISCRIMINANT_CHECK:FAIL

         when 7 =>
            --  Cannot assign to a constant
            null;

         when 8 =>
            Y8 := X; -- @DISCRIMINANT_CHECK:FAIL

         when 9 =>
            Y9 := X; -- @DISCRIMINANT_CHECK:FAIL

         when others =>
            null;
      end case;
      pragma Assert (True);
   end P;

end Test_Immutable;
