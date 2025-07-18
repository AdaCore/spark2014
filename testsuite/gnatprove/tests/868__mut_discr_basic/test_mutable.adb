package body Test_Mutable is

   procedure P (I : Positive; X : T1) is
      Y1  : T1;
      Y2  : T1 := (False, False, 222);
      Y3  : T1 := (Y2 with delta F => 333);
      Y4  : constant T1 := (True, True, 444);
      Y51 : T1 (True, False);
      Y52 : T1 (True, False) := (True, False, 555);
      Y61 : T2;
      Y62 : T2 := (True, False, 666);
      Y7  : constant T1 := Y1'Update(F => 777);
      Y8  : T1 := Y4'Update(F => 888);
      Y9  : T1 := Y51'Update(F => 999);
      -- A safe value of type T2. Constrained object.
      C   : T2 := (True, False, 10101);
      -- A safe value of type T2. Unconstrained object.
      U   : T1 := T2'(True, False, 10101);
   begin

      --  Legal assignments and assertions

      --  Unconstrained objects
      pragma Assert (not Y1'Constrained); --@ASSERT:PASS
      Y1 := X;
      pragma Assert (not Y2'Constrained); --@ASSERT:PASS
      Y2 := X;
      pragma Assert (not Y3'Constrained); --@ASSERT:PASS
      Y3 := X;

      --  The 'constant' keyword makes the object constrained
      pragma Assert (Y4'Constrained); --@ASSERT:PASS
      --  Constrained object
      pragma Assert (Y51'Constrained); --@ASSERT:PASS
      pragma Assert (Y52'Constrained); --@ASSERT:PASS
      --  Constrained type
      pragma Assert (Y61'Constrained); --@ASSERT:PASS
      pragma Assert (Y62'Constrained); --@ASSERT:PASS

      --  'Update creates a new value. The 'Constrained of the source object is
      --  irrelevant.
      pragma Assert (Y7'Constrained); --@ASSERT:PASS
      pragma Assert (not Y8'Constrained); --@ASSERT:PASS
      Y8 := C;
      pragma Assert (not Y9'Constrained); --@ASSERT:PASS
      Y9 := C;

      pragma Assert (C'Constrained); --@ASSERT:PASS
      pragma Assert (not U'Constrained); --@ASSERT:PASS

      --  Possible run-time exceptions

      --  The first non-zero digits of the case selector denote the subject
      --  variable Y#. The lower digits are used to number an interesting case.
      case I is
         when 1001 =>
            pragma Assert (Y1'Constrained); --@ASSERT:FAIL

         when 1002 =>
            Y1 := C;
            pragma Assert (Y1'Constrained); --@ASSERT:FAIL

         when 2001 =>
            pragma Assert (Y2'Constrained); --@ASSERT:FAIL

         when 3001 =>
            pragma Assert (Y3'Constrained); --@ASSERT:FAIL

         when 4001 =>
            pragma Assert (not Y4'Constrained); --@ASSERT:FAIL

         when 5101 =>
            pragma Assert (not Y51'Constrained); --@ASSERT:FAIL

         when 5102 =>
            Y51 := U;
            pragma Assert (Y51'Constrained); --@ASSERT:PASS
            Y51 := X; -- @DISCRIMINANT_CHECK:FAIL

         when 6101 =>
            pragma Assert (not Y61'Constrained); --@ASSERT:FAIL

         when 6102 =>
            Y61 := U;
            pragma Assert (Y61'Constrained); --@ASSERT:PASS
            Y61 := X; -- @DISCRIMINANT_CHECK:FAIL

         when 7001 =>
            pragma Assert (not Y7'Constrained); --@ASSERT:FAIL

         when 8001 =>
            pragma Assert (Y8'Constrained); --@ASSERT:FAIL

         when 9001 =>
            pragma Assert (Y9'Constrained); --@ASSERT:FAIL

         when others =>
            null;
      end case;
      pragma Assert (True);
   end P;

end Test_Mutable;
