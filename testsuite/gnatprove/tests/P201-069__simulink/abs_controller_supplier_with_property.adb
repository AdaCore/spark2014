--  Copyright (C) Your Company Name
--
--  @generated with QGen Code Generator 2.1.0w (20150629)
--  Command line arguments:
--    --from-simulink
--    --language ada
--    --no-misra
--    --clean ABS_Controller_supplier_with_property.mdl
--    --typing C:/home/ibk14/tmp/spark_examples/ABS_Controller_supplier_with_property_types.txt
--    --output ABS_Controller_supplier_with_property.mdl_generated

pragma Style_Checks ("M999");  --  ignore long lines
pragma SPARK_Mode;

with Simulink_Functions; use Simulink_Functions;

package body ABS_Controller_supplier_with_property is

   procedure comp
      (Wheel_Speed : Unsigned_32;
       Vehicle_Speed : Unsigned_32;
       Apply_Brakes : out Integer_32)
   is
      use type Integer_32;
      use type Integer_8;
      use type Unsigned_32;
      Sum_out1 : Integer_32;
      Sum_1_out1 : Integer_8;
      At_Rest_Switch_out1 : Integer_32;
      Sum_1_out1_sat : Integer_32;
   begin
      --  Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Bang-bang\ncontroller/Data Type Conversion1
      --  Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Bang-bang\ncontroller/Relational\nOperator
      --  Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Bang-bang\ncontroller/Data Type Conversion2
      --  Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Bang-bang\ncontroller/Relational\nOperator1
      --  Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Data Type Conversion
      --  Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Wheel Speed\nGain
      --  Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Depress\nBrakes
      --  Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Data Type Conversion1
      --  Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Vehicle Speed\nGain
      --  Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Bang-bang\ncontroller/Constant
      --  Block ABS_Controller_supplier_with_property/Wheel\nSpeed
      --  Block ABS_Controller_supplier_with_property/Vehicle\nSpeed
      --  Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/At Rest\nSwitch

      if (Vehicle_Speed) > (0) then

         --  Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Sum
         Sum_out1 := (Integer_32 ((10) * (Wheel_Speed))) - (Integer_32 ((8) * (Vehicle_Speed)));
         --  End Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Sum

         --  Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Bang-bang\ncontroller/Sum
         Sum_1_out1_sat := Integer_32 ((Boolean_To_Integer_8 ((Sum_out1) > (0))) - (Boolean_To_Integer_8 ((Sum_out1) < (0))));

         if (Sum_1_out1_sat) > (127) then
            Sum_1_out1 := 127;
         else

            if (Sum_1_out1_sat) < ((-128)) then
               Sum_1_out1 := (-128);
            else
               Sum_1_out1 := Integer_8 (Sum_1_out1_sat);
            end if;

         end if;

         --  End Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Bang-bang\ncontroller/Sum
         At_Rest_Switch_out1 := Integer_32 (Sum_1_out1);
      else
         At_Rest_Switch_out1 := 1;
      end if;

      --  End Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/At Rest\nSwitch
      --  End Block ABS_Controller_supplier_with_property/Vehicle\nSpeed
      --  End Block ABS_Controller_supplier_with_property/Wheel\nSpeed
      --  End Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Bang-bang\ncontroller/Constant
      --  End Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Vehicle Speed\nGain
      --  End Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Data Type Conversion1
      --  End Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Depress\nBrakes
      --  End Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Wheel Speed\nGain
      --  End Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Data Type Conversion
      --  End Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Bang-bang\ncontroller/Relational\nOperator1
      --  End Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Bang-bang\ncontroller/Data Type Conversion2
      --  End Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Bang-bang\ncontroller/Relational\nOperator
      --  End Block ABS_Controller_supplier_with_property/ABS_Controller_supplier/Bang-bang\ncontroller/Data Type Conversion1

      --  Block ABS_Controller_supplier_with_property/Implication/Or
      --  Block ABS_Controller_supplier_with_property/At Rest
      --  Block ABS_Controller_supplier_with_property/Vehicle\nSpeed
      --  Block ABS_Controller_supplier_with_property/Implication/Negation
      --  Block ABS_Controller_supplier_with_property/Applies\nBrakes
      --  Block ABS_Controller_supplier_with_property/Consequent:\nApplies Brake\nWhen At Rest
      pragma Assert ((not  ((Vehicle_Speed) = (0)))
         or else ((At_Rest_Switch_out1) = (1)), "Violation of assertion at block ABS_Controller_supplier_with_property/Consequent:\nApplies Brake\nWhen At Rest");
      --  End Block ABS_Controller_supplier_with_property/Consequent:\nApplies Brake\nWhen At Rest
      --  End Block ABS_Controller_supplier_with_property/Applies\nBrakes
      --  End Block ABS_Controller_supplier_with_property/Implication/Negation
      --  End Block ABS_Controller_supplier_with_property/Vehicle\nSpeed
      --  End Block ABS_Controller_supplier_with_property/At Rest
      --  End Block ABS_Controller_supplier_with_property/Implication/Or

      --  Block ABS_Controller_supplier_with_property/Apply\nBrakes
      Apply_Brakes := At_Rest_Switch_out1;
      --  End Block ABS_Controller_supplier_with_property/Apply\nBrakes
   end comp;
end ABS_Controller_supplier_with_property;
--  @EOF
