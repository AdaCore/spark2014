package Subprograms is
   function F1 (Val : Integer) return Integer
     with Contract_Cases => (Val = 0 => F1'Result = 0);
   --  returns 0

   function F1bis (Val : Integer) return Integer
     with Pre => Val = 0,
          Contract_Cases => (Val = 0 => F1bis'Result = 0);

   function F2 (Val : Integer) return Integer
     with Contract_Cases => (Val = 0 => F2'Result = 0);
   --  returns 1

   function F2bis (Val : Integer) return Integer
     with Pre => Val = 0,
          Contract_Cases => (Val = 0 => F2bis'Result = 0);

   function F3 (Val : Integer) return Integer
     with Contract_Cases => (Val >= 0 => F3'Result = 1,
                             Val  = 0 => F3'Result = 2,
                             Val <= 0 => F3'Result = 3);
   --  returns Val

   function F3bis (Val : Integer) return Integer
     with Pre => Val in -1 .. 1,
          Contract_Cases => (Val > 0 => F3bis'Result = 1,
                             Val = 0 => F3bis'Result = 2,
                             Val < 0 => F3bis'Result = 3);

   procedure Incr (Val : in out Integer)
     with Pre => Val /= Integer'Last,
          Contract_Cases => (Val + 1 > 0  => Val = Val'Old + 1,  -- true
                             Val + 1 <= 0 => Val = Val'Old);     -- false
end Subprograms;
