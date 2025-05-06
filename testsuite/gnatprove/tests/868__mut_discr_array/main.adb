procedure Main is

   type R (D : Integer := 0) is record
      F : Integer;
   end record;

   procedure P_Arr_Unconstrained (X : in out R)
   with Pre => X'Constrained;

   procedure P_Arr_Constrained (X : in out R)
   with Pre => not X'Constrained;

   -------------------------
   -- P_Arr_Unconstrained --
   -------------------------

   procedure P_Arr_Unconstrained (X : in out R) is
      Ar : array (1 .. 3) of R := (others => (1, 0));
   begin
      pragma Assert (for all E of Ar => not E'Constrained); -- @ASSERT:PASS

      Ar (2) := X; -- @DISCRIMINANT_CHECK:PASS

      --  Assignment does not change the constrained property. It is still
      --  unconstrained.
      pragma Assert (Ar (2)'Constrained); -- @ASSERT:FAIL

   end P_Arr_Unconstrained;

   -----------------------
   -- P_Arr_Constrained --
   -----------------------

   procedure P_Arr_Constrained (X : in out R) is
      Ar : array (1 .. 3) of R (9) := (others => (9, 0));
   begin
      pragma Assert (for all E of Ar => E'Constrained); -- @ASSERT:PASS

      if X.D /= 9 then
         Ar (2) := X; -- @DISCRIMINANT_CHECK:FAIL

      else
         Ar (2) := X; -- @DISCRIMINANT_CHECK:PASS

         --  Assignment does not change the constrained property. It is still
         --  constrained.
         pragma Assert (not Ar (2)'Constrained); -- @ASSERT:FAIL
      end if;

   end P_Arr_Constrained;

   U1 : R := (1, 111);
   U2 : R := (9, 999);
   C1 : R (2) := (2, 222);
   C2 : R (9) := (9, 999);

begin
   pragma Assert (not U1'Constrained); -- @ASSERT:PASS
   pragma Assert (not U2'Constrained); -- @ASSERT:PASS
   pragma Assert (C1'Constrained); -- @ASSERT:PASS
   pragma Assert (C2'Constrained); -- @ASSERT:PASS

   P_Arr_Unconstrained (C1);
   P_Arr_Unconstrained (C2);
   P_Arr_Constrained (U1);
   P_Arr_Constrained (U2);

end Main;
