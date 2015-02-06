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

   -----------------------------------------
   --  multidimensional unconstrained arrays
   -----------------------------------------

   procedure Test1  (A       : in out AM;
                     X       : in IT1;
                     Y       : in IT2;
                     Z       : in IT3;
                     New_Val : in ET1)
   is
   begin
      A := A'Update ((X, Y, Z) => New_Val);  --  3 falsifiable checks
   end Test1;

   procedure Test3  (A       : in out AM;
                     X       : in IT1;
                     Y       : in IT2;
                     Z       : in IT3;
                     New_Val : in ET1)
   is
   begin
      if X > IT1'First and then Y > IT2'First and then Z < IT3'Last
        and then New_Val < ET1'Last then
         A := A'Update ((X - 1, Y - 1, Z + 1) => New_Val + 1);
      end if;
   end Test3;

   procedure Test4  (A       : in out AM;
                     X1, X2  : in IT1;
                     Y1, Y2  : in IT2;
                     Z1, Z2  : in IT3;
                     New_Val : in ET1)
   is
   begin
      --  6 falsifiable checks
      A := A'Update ((X1, Y1, Z1) | (X2, Y2, Z2) => New_Val);
   end Test4;

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
