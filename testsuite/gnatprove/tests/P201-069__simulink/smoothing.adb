--  Copyright (C) Your Company Name
--
--  @generated with QGen Code Generator 2.1.0w (20150629)
--  Command line arguments:
--    --from-simulink
--    --language ada
--    --clean Smoothing.mdl
--    --typing C:/home/ibk14/tmp/spark_examples/Smoothing_types.txt
--    --output Smoothing.mdl_generated

pragma Style_Checks ("M999");  --  ignore long lines
pragma SPARK_Mode;

package body Smoothing is

   procedure comp
      (New_Value : Long_Float;
       Prior_Value : Long_Float;
       Smoothing_Factor : Long_Float;
       Smoothed_Value : out Long_Float)
   is
      use type Boolean;
      use type Long_Float;
      Abs_Delta_out1 : Long_Float with Ghost;
      Compare_To_Zero_out1 : Boolean with Ghost;
      Smoother_Value_out1 : Long_Float;
      Abs_New_Delta_out1 : Long_Float with Ghost;
   begin
      --  Block Smoothing/Old Delta
      --  Block Smoothing/New\nValue
      --  Block Smoothing/Prior\nValue
      --  Block Smoothing/Abs\nDelta
      Abs_Delta_out1 := abs ((New_Value) - (Prior_Value));
      --  End Block Smoothing/Abs\nDelta
      --  End Block Smoothing/Prior\nValue
      --  End Block Smoothing/New\nValue
      --  End Block Smoothing/Old Delta

      --  Block Smoothing/Compare\nTo Zero
      Compare_To_Zero_out1 := (Abs_Delta_out1) = (0.0E+00);
      --  End Block Smoothing/Compare\nTo Zero

      --  Block Smoothing/Compare\nTo Constant
      --  Block Smoothing/Smoothing\nFactor
      --  Block Smoothing/Antecedent:\nFactor Greater\nThan One
      pragma Assert ((Smoothing_Factor) > (1.0), "Violation of assertion at block Smoothing/Antecedent:\nFactor Greater\nThan One");
      --  End Block Smoothing/Antecedent:\nFactor Greater\nThan One
      --  End Block Smoothing/Smoothing\nFactor
      --  End Block Smoothing/Compare\nTo Constant

      --  Block Smoothing/Smoothing/Compare\nTo Zero
      --  Block Smoothing/Smoothing\nFactor
      --  Block Smoothing/Smoothing/Division\nPre-Condition
      pragma Assert ((Smoothing_Factor) /= (0.0E+00), "Violation of assertion at block Smoothing/Smoothing/Division\nPre-Condition");
      --  End Block Smoothing/Smoothing/Division\nPre-Condition
      --  End Block Smoothing/Smoothing\nFactor
      --  End Block Smoothing/Smoothing/Compare\nTo Zero

      --  Block Smoothing/Smoothing/Smoothed\nDelta
      --  Block Smoothing/Smoothing\nFactor
      --  Block Smoothing/New\nValue
      --  Block Smoothing/Smoothing/Delta
      --  Block Smoothing/Prior\nValue
      --  Block Smoothing/Smoothing/Smoother\nValue
      Smoother_Value_out1 := (Prior_Value) + (((New_Value) - (Prior_Value)) / (Smoothing_Factor));
      --  End Block Smoothing/Smoothing/Smoother\nValue
      --  End Block Smoothing/Prior\nValue
      --  End Block Smoothing/Smoothing/Delta
      --  End Block Smoothing/New\nValue
      --  End Block Smoothing/Smoothing\nFactor
      --  End Block Smoothing/Smoothing/Smoothed\nDelta

      --  Block Smoothing/New\nDelta
      --  Block Smoothing/Prior\nValue
      --  Block Smoothing/Abs\nNew\nDelta
      Abs_New_Delta_out1 := abs ((Smoother_Value_out1) - (Prior_Value));
      --  End Block Smoothing/Abs\nNew\nDelta
      --  End Block Smoothing/Prior\nValue
      --  End Block Smoothing/New\nDelta

      --  Block Smoothing/Implication\n(change)/Or
      --  Block Smoothing/Logical\nOperator
      --  Block Smoothing/Implication\n(change)/Negation
      --  Block Smoothing/Delta\nReduced
      --  Block Smoothing/Consequent:\nSmoothing
      pragma Assert ((not  (not  (Compare_To_Zero_out1)))
         or else ((Abs_New_Delta_out1) < (Abs_Delta_out1)), "Violation of assertion at block Smoothing/Consequent:\nSmoothing");
      --  End Block Smoothing/Consequent:\nSmoothing
      --  End Block Smoothing/Delta\nReduced
      --  End Block Smoothing/Implication\n(change)/Negation
      --  End Block Smoothing/Logical\nOperator
      --  End Block Smoothing/Implication\n(change)/Or

      --  Block Smoothing/Implication\n(no change)/Or
      --  Block Smoothing/Implication\n(no change)/Negation
      --  Block Smoothing/No\nChange
      --  Block Smoothing/Consequent:\nNo Change
      pragma Assert ((not  (Compare_To_Zero_out1))
         or else ((Abs_New_Delta_out1) = (0.0E+00)), "Violation of assertion at block Smoothing/Consequent:\nNo Change");
      --  End Block Smoothing/Consequent:\nNo Change
      --  End Block Smoothing/No\nChange
      --  End Block Smoothing/Implication\n(no change)/Negation
      --  End Block Smoothing/Implication\n(no change)/Or

      --  Block Smoothing/Smoothed\nValue
      Smoothed_Value := Smoother_Value_out1;
      --  End Block Smoothing/Smoothed\nValue
   end comp;
end Smoothing;
--  @EOF
