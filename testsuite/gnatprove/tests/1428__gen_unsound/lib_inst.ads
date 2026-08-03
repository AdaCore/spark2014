with More;

--  Variant 3: library-level instance of a generic subprogram, which is
--  affected just like the local ones.

package Lib_Inst
  with SPARK_Mode
is

   function Inst is new More.Gen_Fun (D => (X => 0));  --@PREDICATE_CHECK:FAIL

end Lib_Inst;
