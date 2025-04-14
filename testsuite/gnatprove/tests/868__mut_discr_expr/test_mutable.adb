package body Test_Mutable is

   procedure P_Only_Constrained (X : out T1);
   -- There is no preconition. We want all calls to be analyzed.

   procedure P_Only_Unconstrained (X : out T1);
   -- There is no preconition. We want all calls to be analyzed.

   ------------------------
   -- P_Only_Constrained --
   ------------------------

   procedure P_Only_Constrained (X : out T1) is
   begin
      pragma Assert (X'Constrained); -- @ASSERT:FAIL
      X.F := 4444;
   end P_Only_Constrained;

   --------------------------
   -- P_Only_Unconstrained --
   --------------------------

   procedure P_Only_Unconstrained (X : out T1) is
   begin
      pragma Assert (not X'Constrained); -- @ASSERT:FAIL
      X.F := 5555;
   end P_Only_Unconstrained;

   -------
   -- P --
   -------

   procedure P (I : Positive) is
      Y1 : T1 := (True, True, 10101);
      Y2 : T2 := (True, False, 20202);
   begin

      --  Unconstrained object
      pragma Assert (not Y1'Constrained); -- @ASSERT:PASS

      --  Constrained object
      pragma Assert (Y2'Constrained); -- @ASSERT:PASS

      --  Expressions are always statically constrained
      pragma Assert (T1'(Y1)'Constrained); -- @ASSERT:PASS

      case I is
         when 1 =>
            --  Expressions are always statically constrained
            pragma Assert (not T1'(Y1)'Constrained); -- @ASSERT:FAIL

         when 2 =>
            --  A value conversion is statically constrained
            pragma Assert (T1 (Y1)'Constrained); -- @ASSERT:PASS

         when 3 =>
            --  A value conversion is statically constrained
            pragma Assert (not T1 (Y1)'Constrained); -- @ASSERT:FAIL

         when 4 =>
            --  A view conversion does not make an unconstrained object
            --  constrained if the target subtype isn't constrained
            P_Only_Constrained (T1 (Y1));

         when 5 =>
            --  A view conversion does not make a constrained object
            --  unconstrained
            P_Only_Unconstrained (T1 (Y2));

         when 6 =>
            --  A view conversion does not make an unconstrained object
            --  constrained if the target subtype isn't constrained
            P_Only_Constrained (T1 (Y1));

         when 7 =>
            --  A view conversion makes an unconstrained object
            --  constrained if the target subtype is constrained
            P_Only_Unconstrained (T2 (Y1));

         when others =>
            null;
      end case;
      pragma Assert (True);
   end P;

end Test_Mutable;
