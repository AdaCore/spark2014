with Private_Discr; use Private_Discr;
package body Discr with SPARK_Mode is

   procedure R1 (C : Natural) is
      D : No_Default := (C => C);
   begin
      D := (C => C);
      D := (C => 0); -- @DISCRIMINANT_CHECK:FAIL
   end R1;

   procedure R2 (C : Natural) is

      D  : With_Default := (C => C);
      D1 : With_Default (C);
      D2 : With_Default;
   begin
      pragma Assert (not D'Constrained);
      pragma Assert (D1'Constrained);
      pragma Assert (D = D1);
      D := (C => C);
      D := (C => 0);
      pragma Assert (not D2'Constrained);
      pragma Assert (D2.C = 0);
      D2 := (C => C);
   end R2;

   procedure R3 (C : Natural) is
      D : With_Default (C);
   begin
      D := (C => C);
      D := (C => 0); -- @DISCRIMINANT_CHECK:FAIL
   end R3;

   procedure R4 (C : Natural) is
      D1 : With_Default := (C => C);
      D2 : With_Default (C) := (C => C);

      procedure Nested1 (D : in out With_Default) with
        Pre => True;

      procedure Nested1 (D : in out With_Default) is
      begin
         D := (C => 0); -- @DISCRIMINANT_CHECK:FAIL
      end Nested1;

      procedure Nested2 (D : in out With_Default) with
        Pre => not D'Constrained;

      procedure Nested2 (D : in out With_Default) is
      begin
         D := (C => 0);
      end Nested2;

   begin
      Nested1 (D1);
      Nested1 (D2);
      Nested2 (D1);
      Nested2 (D2); -- @PRECONDITION:FAIL
   end R4;

   procedure R5 (C : Natural) is
      D1 : With_Default (C) := (C => C);
      D2 : With_Default := (C => C);
      H  : Holder;
   begin
      pragma Assert (H.Content.C = 0);
      pragma Assert (not H.Content'Constrained);
      H.Content := D1;
      pragma Assert (not H.Content'Constrained);
      pragma Assert (H.Content.C = C);
      H.Content := D2;
      pragma Assert (not H.Content'Constrained);
      pragma Assert (H.Content.C = C);
   end R5;

   procedure R6 (C : Natural) is
      type With_Bad_Default1 (D : Natural := C + 1) is null record; -- @OVERFLOW_CHECK:FAIL
      D1 : With_Bad_Default1;

      function F (X : Natural) return Natural is (X - 1) with
        Pre => X > 0;

      type With_Bad_Default2 (D : Natural := F (C)) is null record; -- @PRECONDITION:FAIL
      D2 : With_Bad_Default2;
   begin
      null;
   end R6;

   procedure P1 (C : Natural) is
      D : P_No_Default := New_No_Default (C);
   begin
      D := New_No_Default (C);
      D := New_No_Default (0); -- @DISCRIMINANT_CHECK:FAIL
   end P1;

   procedure P2 (C : Natural) is

      D  : P_With_Default := New_With_Default (C);
      D1 : P_With_Default (C);
      D2 : P_With_Default;
   begin
      pragma Assert (not D'Constrained);
      pragma Assert (D1'Constrained);
      D := New_With_Default (C);
      D := New_With_Default (0);
      pragma Assert (not D2'Constrained);
      pragma Assert (D2.C = 0);
      D2 := New_With_Default (C);
   end P2;

   procedure P3 (C : Natural) is
      D : P_With_Default (C);
   begin
      D := New_With_Default (C);
      D := New_With_Default (0); -- @DISCRIMINANT_CHECK:FAIL
   end P3;

   procedure P4 (C : Natural) is
      D1 : P_With_Default := New_With_Default (C);
      D2 : P_With_Default (C) := New_With_Default (C);

      procedure Nested1 (D : in out P_With_Default) with
        Pre => True;

      procedure Nested1 (D : in out P_With_Default) is
      begin
         D := New_With_Default (0); -- @DISCRIMINANT_CHECK:FAIL
      end Nested1;

      procedure Nested2 (D : in out P_With_Default) with
        Pre => not D'Constrained;

      procedure Nested2 (D : in out P_With_Default) is
      begin
         D := New_With_Default (0);
      end Nested2;

   begin
      Nested1 (D1);
      Nested1 (D2);
      Nested2 (D1);
      Nested2 (D2); -- @PRECONDITION:FAIL
   end P4;

   procedure P5 (C : Natural) is
      D1 : P_With_Default (C) := New_With_Default (C);
      D2 : P_With_Default := New_With_Default (C);
      H  : P_Holder;
   begin
      pragma Assert (H.Content.C = 0);
      pragma Assert (not H.Content'Constrained);
      H.Content := D1;
      pragma Assert (not H.Content'Constrained);
      pragma Assert (H.Content.C = C);
      H.Content := D2;
      pragma Assert (not H.Content'Constrained);
      pragma Assert (H.Content.C = C);
   end P5;

end Discr;
