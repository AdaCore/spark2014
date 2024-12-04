package Subprograms is
   function F1 (Val : Integer) return Integer
     with Contract_Cases => (Val = 0 => F1'Result = 0); --@COMPLETE_CASES:FAIL
   --  returns 0

   function F1bis (Val : Integer) return Integer
     with Pre => Val = 0,
          Contract_Cases => (Val = 0 => F1bis'Result = 0); --@COMPLETE_CASES:PASS

   function F2 (Val : Integer) return Integer
     with Contract_Cases => (Val = 0 => F2'Result = 0); --@CONTRACT_CASE:FAIL @COMPLETE_CASES:FAIL
   --  returns 1

   function F2bis (Val : Integer) return Integer
     with Pre => Val = 0,
          Contract_Cases => (Val = 0 => F2bis'Result = 0); --@CONTRACT_CASE:PASS @COMPLETE_CASES:PASS

   function F3 (Val : Integer) return Integer
     with Contract_Cases => (Val >= 0 => F3'Result = 1, --@CONTRACT_CASE:FAIL @DISJOINT_CASES:FAIL
                             Val  = 0 => F3'Result = 2,
                             Val <= 0 => F3'Result = 3); --@CONTRACT_CASE:FAIL
   --  returns Val

   function F3bis (Val : Integer) return Integer
     with Pre => Val in -1 .. 1,
          Contract_Cases => (Val > 0 => F3bis'Result = 1, --@CONTRACT_CASE:PASS @DISJOINT_CASES:PASS @COMPLETE_CASES:PASS
                             Val = 0 => F3bis'Result = 2, --@CONTRACT_CASE:PASS
                             Val < 0 => F3bis'Result = 3); --@CONTRACT_CASE:PASS

   procedure Incr (Val : in out Integer)
     with Pre => Val /= Integer'Last,
          Contract_Cases => (Val + 1 > 0  => Val = Val'Old + 1, --@CONTRACT_CASE:PASS @DISJOINT_CASES:PASS @COMPLETE_CASES:PASS
                             Val + 1 <= 0 => Val = Val'Old); --@CONTRACT_CASE:FAIL
end Subprograms;
