--  Copyright (C) Your Company Name
--
--  @generated with QGen Code Generator 2.1.0w (20150629)
--  Command line arguments:
--    --from-simulink
--    --language ada
--    --clean DynamicSaturateAssert.mdl
--    --typing C:/home/ibk14/tmp/spark_examples/DynamicSaturateAssert_types.txt
--    --output DynamicSaturateAssert.mdl_generated

pragma Style_Checks ("M999");  --  ignore long lines
pragma SPARK_Mode;

package body DynamicSaturateAssert is

   procedure comp
      (Value : Unsigned_32_m1_0_M100_0;
       Max : Unsigned_32_m1_0_M100_0;
       Min : Unsigned_32_m1_0_M100_0;
       Saturated_Value : out Unsigned_32)
   is
      use type Unsigned_32;
      use type Unsigned_32_m1_0_M100_0;
      Saturation_Dynamic_out1 : Unsigned_32;
   begin
      --  Block DynamicSaturateAssert/Value
      --  Block DynamicSaturateAssert/Min
      --  Block DynamicSaturateAssert/Max
      --  Block DynamicSaturateAssert/Saturation\nDynamic

      if (Value) < (Min) then
         Saturation_Dynamic_out1 := Min;
      else

         if (Value) > (Max) then
            Saturation_Dynamic_out1 := Max;
         else
            Saturation_Dynamic_out1 := Value;
         end if;

      end if;

      --  End Block DynamicSaturateAssert/Saturation\nDynamic
      --  End Block DynamicSaturateAssert/Max
      --  End Block DynamicSaturateAssert/Min
      --  End Block DynamicSaturateAssert/Value

      --  Block DynamicSaturateAssert/Saturated\nValue
      Saturated_Value := Saturation_Dynamic_out1;
      --  End Block DynamicSaturateAssert/Saturated\nValue

      --  Block DynamicSaturateAssert/Logical\nOperator
      --  Block DynamicSaturateAssert/Min
      --  Block DynamicSaturateAssert/Greater\nThan Min
      --  Block DynamicSaturateAssert/Max
      --  Block DynamicSaturateAssert/Less\nThan Max
      --  Block DynamicSaturateAssert/In Between\nPost-Condition
      pragma Assert (((Saturation_Dynamic_out1) <= (Max))
         and then ((Saturation_Dynamic_out1) >= (Min)), "Violation of assertion at block DynamicSaturateAssert/In Between\nPost-Condition");
      --  End Block DynamicSaturateAssert/In Between\nPost-Condition
      --  End Block DynamicSaturateAssert/Less\nThan Max
      --  End Block DynamicSaturateAssert/Max
      --  End Block DynamicSaturateAssert/Greater\nThan Min
      --  End Block DynamicSaturateAssert/Min
      --  End Block DynamicSaturateAssert/Logical\nOperator

      --  Block DynamicSaturateAssert/Max Greater\nThan Min
      --  Block DynamicSaturateAssert/Max
      --  Block DynamicSaturateAssert/Min
      --  Block DynamicSaturateAssert/In Between\nPre-Condition
      pragma Assert ((Max) >= (Min), "Violation of assertion at block DynamicSaturateAssert/In Between\nPre-Condition");
      --  End Block DynamicSaturateAssert/In Between\nPre-Condition
      --  End Block DynamicSaturateAssert/Min
      --  End Block DynamicSaturateAssert/Max
      --  End Block DynamicSaturateAssert/Max Greater\nThan Min
   end comp;
end DynamicSaturateAssert;
--  @EOF
