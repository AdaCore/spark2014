package Type_Declarations_Illegal
  with SPARK_Mode
is
   --  TU: 1. Access type declarations are not permitted in |SPARK|.
   --  [This follows from the rule forbidding use of the Ada reserved
   --  word **access**, which also disallows all forms of anonymous
   --  access types.]
   type Integer_P is access Integer;  --  Access types are not in SPARK
end Type_Declarations_Illegal;
