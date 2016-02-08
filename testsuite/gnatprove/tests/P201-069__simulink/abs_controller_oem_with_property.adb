--  Copyright (C) Your Company Name
--
--  @generated with QGen Code Generator 2.1.0w (20150629)
--  Command line arguments:
--    --from-simulink
--    --language ada
--    --no-misra
--    --clean ABS_Controller_oem_with_property.mdl
--    --typing C:/home/ibk14/tmp/spark_examples/ABS_Controller_oem_with_property_types.txt
--    --output ABS_Controller_oem_with_property.mdl_generated

pragma Style_Checks ("M999");  --  ignore long lines
pragma SPARK_Mode;

with Simulink_Functions; use Simulink_Functions;

package body ABS_Controller_oem_with_property is

   procedure comp
      (Wheel_Speed : Long_Float;
       Vehicle_Speed : Long_Float;
       Apply_Brakes : out Long_Float)
   is
      use type Long_Float;
      EpsIfZero_out1 : Long_Float;
      Diff_out1 : Long_Float;
      Difference_out1 : Long_Float;
      Sum_out1 : Long_Float;
   begin
      --  Block ABS_Controller_oem_with_property/Non-Zero\nWheel Speed
      --  Block ABS_Controller_oem_with_property/Wheel\nSpeed
      --  Block ABS_Controller_oem_with_property/Applies Brake\nWhen At Rest\nAntecedent
      pragma Assert ((Wheel_Speed) >= (2.2204e-16), "Violation of assertion at block ABS_Controller_oem_with_property/Applies Brake\nWhen At Rest\nAntecedent");
      --  End Block ABS_Controller_oem_with_property/Applies Brake\nWhen At Rest\nAntecedent
      --  End Block ABS_Controller_oem_with_property/Wheel\nSpeed
      --  End Block ABS_Controller_oem_with_property/Non-Zero\nWheel Speed

      --  Block ABS_Controller_oem_with_property/ABS_Controller_oem/eps
      --  Block ABS_Controller_oem_with_property/Vehicle\nSpeed
      --  Block ABS_Controller_oem_with_property/ABS_Controller_oem/EpsIfZero

      if (Vehicle_Speed) /= (0.0E+00) then
         EpsIfZero_out1 := Vehicle_Speed;
      else
         EpsIfZero_out1 := 2.2204e-16;
      end if;

      --  End Block ABS_Controller_oem_with_property/ABS_Controller_oem/EpsIfZero
      --  End Block ABS_Controller_oem_with_property/Vehicle\nSpeed
      --  End Block ABS_Controller_oem_with_property/ABS_Controller_oem/eps

      --  Block ABS_Controller_oem_with_property/ABS_Controller_oem/Divide
      --  Block ABS_Controller_oem_with_property/Wheel\nSpeed
      --  Block ABS_Controller_oem_with_property/ABS_Controller_oem/One
      --  Block ABS_Controller_oem_with_property/ABS_Controller_oem/Diff
      Diff_out1 := (1.0) - ((Wheel_Speed) / (EpsIfZero_out1));
      --  End Block ABS_Controller_oem_with_property/ABS_Controller_oem/Diff
      --  End Block ABS_Controller_oem_with_property/ABS_Controller_oem/One
      --  End Block ABS_Controller_oem_with_property/Wheel\nSpeed
      --  End Block ABS_Controller_oem_with_property/ABS_Controller_oem/Divide

      --  Block ABS_Controller_oem_with_property/ABS_Controller_oem/Desired\nrelative\nslip
      --  Block ABS_Controller_oem_with_property/ABS_Controller_oem/Difference
      Difference_out1 := (0.2) - (Diff_out1);
      --  End Block ABS_Controller_oem_with_property/ABS_Controller_oem/Difference
      --  End Block ABS_Controller_oem_with_property/ABS_Controller_oem/Desired\nrelative\nslip

      --  Block ABS_Controller_oem_with_property/ABS_Controller_oem/Bang-bang\ncontroller/Data Type Conversion2
      --  Block ABS_Controller_oem_with_property/ABS_Controller_oem/Bang-bang\ncontroller/Relational\nOperator1
      --  Block ABS_Controller_oem_with_property/ABS_Controller_oem/Bang-bang\ncontroller/Data Type Conversion1
      --  Block ABS_Controller_oem_with_property/ABS_Controller_oem/Bang-bang\ncontroller/Constant
      --  Block ABS_Controller_oem_with_property/ABS_Controller_oem/Bang-bang\ncontroller/Relational\nOperator
      --  Block ABS_Controller_oem_with_property/ABS_Controller_oem/Bang-bang\ncontroller/Sum
      Sum_out1 := (Boolean_To_Long_Float ((Difference_out1) > (0.0))) - (Boolean_To_Long_Float ((Difference_out1) < (0.0)));
      --  End Block ABS_Controller_oem_with_property/ABS_Controller_oem/Bang-bang\ncontroller/Sum
      --  End Block ABS_Controller_oem_with_property/ABS_Controller_oem/Bang-bang\ncontroller/Relational\nOperator
      --  End Block ABS_Controller_oem_with_property/ABS_Controller_oem/Bang-bang\ncontroller/Constant
      --  End Block ABS_Controller_oem_with_property/ABS_Controller_oem/Bang-bang\ncontroller/Data Type Conversion1
      --  End Block ABS_Controller_oem_with_property/ABS_Controller_oem/Bang-bang\ncontroller/Relational\nOperator1
      --  End Block ABS_Controller_oem_with_property/ABS_Controller_oem/Bang-bang\ncontroller/Data Type Conversion2

      --  Block ABS_Controller_oem_with_property/Implication/Or
      --  Block ABS_Controller_oem_with_property/At Rest
      --  Block ABS_Controller_oem_with_property/Vehicle\nSpeed
      --  Block ABS_Controller_oem_with_property/Implication/Negation
      --  Block ABS_Controller_oem_with_property/Compare\nTo On
      --  Block ABS_Controller_oem_with_property/Applies Brake\nWhen At Rest\nConsequent
      pragma Assert ((not  ((Vehicle_Speed) = (0.0E+00)))
         or else ((Sum_out1) = (1.0)), "Violation of assertion at block ABS_Controller_oem_with_property/Applies Brake\nWhen At Rest\nConsequent");
      --  End Block ABS_Controller_oem_with_property/Applies Brake\nWhen At Rest\nConsequent
      --  End Block ABS_Controller_oem_with_property/Compare\nTo On
      --  End Block ABS_Controller_oem_with_property/Implication/Negation
      --  End Block ABS_Controller_oem_with_property/Vehicle\nSpeed
      --  End Block ABS_Controller_oem_with_property/At Rest
      --  End Block ABS_Controller_oem_with_property/Implication/Or

      --  Block ABS_Controller_oem_with_property/Apply\nBrakes
      Apply_Brakes := Sum_out1;
      --  End Block ABS_Controller_oem_with_property/Apply\nBrakes
   end comp;
end ABS_Controller_oem_with_property;
--  @EOF
