package body Update_Checks_1 is

   --------------------------------------------------------------
   --  single dimensional unconstrained arrays, falsifiable tests
   --------------------------------------------------------------

   procedure P1 (A: in out Array_U; I : in Index; New_Val : in Integer) is
   begin
      A := A'Update(I => New_Val); -- failed check of I expected
   end P1;

   procedure P2 (A: in out Array_U; I : in Index; New_Val : in Integer) is
   begin
      A := A'Update(I + 1 => New_Val); -- failed check of I + 1 expected
   end P2;

   procedure P4 (A: in out Array_U; I : in Index; New_Val : in Integer) is
   begin
      A := A'Update(1 .. I => New_Val); --  failed check of I expected
   end P4;

   procedure P5
     (A: in out Array_U; I, J, K, L : in Index; New_Val : in Integer) is
   begin
      --  4 failed checks expected:
      A := A'Update (1 .. I => 0, J .. K | L => New_Val);
   end P5;

   procedure P6
     (A: in out Array_U; New_Val : in Integer) is
   begin
      --  failed check of Index'Range expected:
      A := A'Update (Index'Range => New_Val);
   end P6;

   --  produces non-healthy mlw, why3 crashes:
   --
   --  procedure P7
   --    (A: out Array_U; New_Val : in Integer) is
   --  begin
   --     --  failed check of Index'Range expected
   --     A := Array_U' (Sub_Index'Range => 0)'Update (Index'Range => New_Val);
   --  end P7;

   --------------------------------------------------------
   --  single dimensional unconstrained arrays, valid tests
   --------------------------------------------------------

   procedure P8 (A: in out Array_U; I : in Index; New_Val : in Integer) is
   begin
      A := A'Update(I => New_Val); -- valid check, precondition
   end P8;

   -------------------------------------------------------------------
   --  Reference tests, to compare generated why and avoid regressions
   -------------------------------------------------------------------

   --  assignment to indexed component of unconstrained array
   procedure Ref_Test_0
     (A: in out Array_U; I : in Index; New_Val : in Integer) is
   begin
      A (I) := New_Val; --  failed index check
   end Ref_Test_0;

   --  assignment to slice of unconstrained array
   procedure Ref_Test_1
     (A: in out Array_U; I : in Index; New_Val : in Integer) is
   begin
      A (2 .. I) := (2 .. I => New_Val); --  expected failed checks, 4 missing
   end Ref_Test_1;

   --  'Update of constrained array with index subtype
   procedure Ref_Test_2
     (A: in out Array_C; I : in Index; New_Val : in Integer) is
   begin
      A := A'Update(I => New_Val); --  failed check
   end Ref_Test_2;

   --  'Update of constrained array, valid index
   procedure Ref_Test_3
     (A: in out Array_C2; I : in Index; New_Val : in Integer) is
   begin
      A := A'Update(I => New_Val);  -- trivially valid/ no check
   end Ref_Test_3;

end Update_Checks_1;
