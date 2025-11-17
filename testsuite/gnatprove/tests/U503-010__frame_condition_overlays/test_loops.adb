procedure Test_Loops
  with SPARK_Mode => On
is
   function Rand (X : Integer) return Boolean with Import, Global => null;

   type R is record
      F, G : Integer;
   end record;

   X : aliased R := (12, 12);
   Y : aliased R := (14, 14) with Address => X'Address;
   Z : aliased R with Import, Address => X'Address;
   V : aliased R with Import, Address => Y'Address;

begin
   --  Test that overlays are handled soundly in the generation of frame
   --  conditions. If a single object (an overlaid object or the root) is
   --  modified in the loop then the frame condition should be generated for
   --  it (but not for other overlaid objects). If more than one overlaid
   --  object is modfied in the loop, then no frame conditions should be
   --  generated.

   declare
      CX : constant R := X;
      CY : constant R := Y;
   begin
      for I in 1 .. 100 loop
         X.F := 0;
         pragma Loop_Invariant (True);
      end loop;
      pragma Assert (X.G = CX.G); -- @ASSERT:PASS
      pragma Assert (if Rand (1) then Y.G = CY.G); -- @ASSERT:FAIL
   end;

   declare
      CX : constant R := X;
      CY : constant R := Y;
      CZ : constant R := Z;
   begin
      for I in 1 .. 100 loop
         Y.F := 0;
         pragma Loop_Invariant (True);
      end loop;
      pragma Assert (Y.G = CY.G); -- @ASSERT:PASS
      pragma Assert (if Rand (2) then X.G = CX.G); -- @ASSERT:FAIL
      pragma Assert (if Rand (3) then Z.F = CZ.F); -- @ASSERT:FAIL
   end;

   declare
      CX : constant R := X;
      CY : constant R := Y;
      CZ : constant R := Z;
   begin
      for I in 1 .. 100 loop
         Y.F := 0;
         X.G := 0;
         pragma Loop_Invariant (True);
      end loop;
      pragma Assert (if Rand (4) then Y.G = CY.G); -- @ASSERT:FAIL
      pragma Assert (if Rand (5) then X.F = CX.F); -- @ASSERT:FAIL
      pragma Assert (if Rand (6) then Z.F = CZ.F); -- @ASSERT:FAIL
   end;

   declare
      CX : constant R := X;
      CZ : constant R := Z;
      CY : constant R := Y;
   begin
      for I in 1 .. 100 loop
         Y.F := 0;
         Z.G := 0;
         pragma Loop_Invariant (True);
      end loop;
      pragma Assert (if Rand (7) then Y.G = CY.G); -- @ASSERT:FAIL
      pragma Assert (if Rand (8) then Z.F = CZ.F); -- @ASSERT:FAIL
      pragma Assert (if Rand (9) then X.F = CX.F); -- @ASSERT:FAIL
   end;

   declare
      CX : constant R := X;
      CZ : constant R := Z;
      CY : constant R := Y;
      CV : constant R := V;
   begin
      for I in 1 .. 100 loop
         Y.F := 0;
         Z.G := 0;
         V.G := 0;
         pragma Loop_Invariant (True);
      end loop;
      pragma Assert (if Rand (10) then Y.G = CY.G); -- @ASSERT:FAIL
      pragma Assert (if Rand (11) then Z.F = CZ.F); -- @ASSERT:FAIL
      pragma Assert (if Rand (12) then V.F = CV.F); -- @ASSERT:FAIL
      pragma Assert (if Rand (13) then X.F = CX.F); -- @ASSERT:FAIL
   end;
end;
