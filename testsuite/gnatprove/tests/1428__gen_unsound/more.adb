package body More
  with SPARK_Mode
is

   function Zero return Integer
   is (0);

   function Gen_Fun return T
   is (D);

   function Gen_Pos return Positive
   is (D);

   --  Variant 1: local instance of a generic function, predicate check
   function Use_Fun return T is
      function Inst is new Gen_Fun (D => (X => 0));  --@PREDICATE_CHECK:FAIL
   begin
      return Inst;
   end Use_Fun;

   --  Variant 2: local instance of a generic function, plain range check. The
   --  problem is not specific to predicates.
   function Use_Pos return Positive is
      function Inst is new Gen_Pos (D => Zero);  --@RANGE_CHECK:FAIL
   begin
      return Inst;
   end Use_Pos;

   --  Control: local instance of a generic package
   function Use_Pkg return T is
      package Inst is new Gen_Pkg (D => (X => 0));  --@PREDICATE_CHECK:FAIL
   begin
      return Inst.F;
   end Use_Pkg;

end More;
