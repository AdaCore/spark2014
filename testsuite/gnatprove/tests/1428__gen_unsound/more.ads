--  Variants around the same soundness problem. Only the instantiations of
--  generic *subprograms* were affected, because the front end wraps those in a
--  wrapper package; the generic package instantiations below are controls that
--  were already reported correctly.

package More
  with SPARK_Mode
is

   type T is record
      X : Integer;
   end record
   with Predicate => X = 1;

   function Zero return Integer
   with Post => Zero'Result = 0;

   generic
      D : T;
   function Gen_Fun return T;

   generic
      D : Positive;
   function Gen_Pos return Positive;

   generic
      D : T;
   package Gen_Pkg is
      function F return T
      is (D);
   end Gen_Pkg;

   --  Control: library-level instance of a generic package
   package Lib_Pkg_Inst is new
     Gen_Pkg (D => (X => 0));  --@PREDICATE_CHECK:FAIL

   function Use_Fun return T;
   function Use_Pos return Positive;
   function Use_Pkg return T;

end More;
