package body Test is

   procedure P (I : Positive; X : T1) is
      -- A safe value of type T2. Constrained object.
      Z : T2 := (True, False, 10101);
      -- A safe value of type T2. Unconstrained object.
      U : T1 := T2'(True, False, 20202);

      Y11 : Nested_U := (R => U);
      Y12 : Nested_U := (R => Z);
      Y13 : Nested_U;
      Y14 : Nested_U;

      Y21 : Nested_C := (R => U);
      Y22 : Nested_C := (R => Z);
      Y23 : Nested_C;
      Y24 : Nested_C;
   begin

      --  Legal assignments and assertions

      Y13 := (R => U);
      Y14 := (R => Z);

      pragma Assert (not Y11.R'Constrained); --@ASSERT:PASS
      pragma Assert (not Y12.R'Constrained); --@ASSERT:PASS
      pragma Assert (not Y13.R'Constrained); --@ASSERT:PASS
      pragma Assert (not Y14.R'Constrained); --@ASSERT:PASS

      Y23 := (R => U);
      Y24 := (R => Z);

      Y11.R := X;
      Y12.R := X;
      Y13.R := X;
      Y14.R := X;

      pragma Assert (Y21.R'Constrained); --@ASSERT:PASS
      pragma Assert (Y22.R'Constrained); --@ASSERT:PASS
      pragma Assert (Y23.R'Constrained); --@ASSERT:PASS
      pragma Assert (Y24.R'Constrained); --@ASSERT:PASS

      --  Possible run-time exceptions

      --  The first non-zero digits of the case selector denote the subject
      --  variable Y#. The lower digits are used to number an interesting case.
      case I is
         when 1101 =>
            pragma Assert (Y11.R'Constrained); --@ASSERT:FAIL

         when 1201 =>
            pragma Assert (Y12.R'Constrained); --@ASSERT:FAIL

         when 1301 =>
            pragma Assert (Y13.R'Constrained); --@ASSERT:FAIL

         when 1401 =>
            pragma Assert (Y14.R'Constrained); --@ASSERT:FAIL

         when 2101 =>
            pragma Assert (not Y21.R'Constrained); --@ASSERT:FAIL

         when 2102 =>
            Y21.R := X; --@DISCRIMINANT_CHECK:FAIL

         when 2201 =>
            pragma Assert (not Y22.R'Constrained); --@ASSERT:FAIL

         when 2202 =>
            Y22.R := X; --@DISCRIMINANT_CHECK:FAIL

         when 2301 =>
            pragma Assert (not Y23.R'Constrained); --@ASSERT:FAIL

         when 2302 =>
            Y23.R := X; --@DISCRIMINANT_CHECK:FAIL

         when 2401 =>
            pragma Assert (not Y24.R'Constrained); --@ASSERT:FAIL

         when 2402 =>
            Y24.R := X; --@DISCRIMINANT_CHECK:FAIL

         when others =>
            null;
      end case;
      pragma Assert (True);
   end P;

end Test;
