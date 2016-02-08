--  Copyright (C) Your Company Name
--
--  @generated with QGen Code Generator 2.1.0w (20150629)
--  Command line arguments:
--    --from-simulink
--    --language ada
--    --clean BiasedDivide.mdl
--    --typing C:/home/ibk14/tmp/spark_examples/BiasedDivide_types.txt
--    --output BiasedDivide.mdl_generated

pragma Style_Checks ("M999");  --  ignore long lines
pragma SPARK_Mode;

package body BiasedDivide is

   procedure comp (y : Long_Float; z : Long_Float; r : out Long_Float) is
      use type Long_Float;
   begin
      --  Block BiasedDivide/Divide
      --  Block BiasedDivide/y
      --  Block BiasedDivide/z
      --  Block BiasedDivide/Bias
      --  Block BiasedDivide/r₂
      r := (y) / ((z) + (-(4.0)));
      --  End Block BiasedDivide/r₂
      --  End Block BiasedDivide/Bias
      --  End Block BiasedDivide/z
      --  End Block BiasedDivide/y
      --  End Block BiasedDivide/Divide
   end comp;
end BiasedDivide;
--  @EOF
