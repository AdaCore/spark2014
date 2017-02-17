--  Copyright (C) Project P consortium
--
--  @generated with GNAT Model Compiler 1.0w
--  Command line arguments:
--
--    --clean nose_gear.mdl
--    --typing nose_gear_types.txt
--    --matlab nose_gear_def.m
--    --language ada

pragma Style_Checks ("M999");  --  ignore long lines
with nose_gear_params; use nose_gear_params;

package body nose_gear is
   Old_NGClickTime_memory : Unsigned_16;
   Old_NGRotations_memory : Unsigned_16;
   Old_estimatedGroundVelocity_memory : Long_Float;

   procedure nose_gear_init is
   begin
      nose_gear.nose_gear_initStates;
   end nose_gear_init;

   procedure nose_gear_initStates is
   begin
      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Old NGClickTime>
      Old_NGClickTime_memory := 0;
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Old NGClickTime>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Old NGRotations>
      Old_NGRotations_memory := 0;
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Old NGRotations>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Old estimatedGroundVelocity>
      Old_estimatedGroundVelocity_memory := 0.0E+00;
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Old estimatedGroundVelocity>
   end nose_gear_initStates;

   procedure nose_gear_comp
      (NGRotations : Unsigned_16;
       NGClickTime : Unsigned_16;
       Millisecs : Unsigned_16;
       estimatedGroundVelocity : out Long_Float;
       estimatedGroundVelocityIsAvailable : out Boolean)
   is
      pragma Warnings (Off, "unused assignment");

      use type Boolean;
      use type Integer_32;
      use type Long_Float;
      use type Unsigned_16;
      Old_NGClickTime_out1 : Unsigned_16;
      Old_NGRotations_out1 : Unsigned_16;
      Old_estimatedGroundVelocity_out1 : Long_Float;
      Max_uint16_out1 : Integer_32;
      Max_uint16_1_out1 : Integer_32;
      Max_uint16_2_out1 : Integer_32;
      Millisecs_out1 : Unsigned_16;
      NGClickTime_out1 : Unsigned_16;
      NGRotations_out1 : Unsigned_16;
      Wheel_Circunference_out1 : Long_Float;
      ms_in_hour_out1 : Long_Float;
      ms_in_our1_out1 : Long_Float;
      Update_Period_OS_interrupt_out1 : Unsigned_16;
      Validity_Period_out1 : Unsigned_16;
      To_int32_Left_out1 : Integer_32;
      To_int32_Left_1_out1 : Integer_32;
      To_int32_Left_2_out1 : Integer_32;
      To_int32_Right_out1 : Integer_32;
      To_int32_Right_1_out1 : Integer_32;
      To_int32_Right_2_out1 : Integer_32;
      Data_Type_Conversion1_out1 : Integer_32;
      Data_Type_Conversion_out1 : Integer_32;
      Sum1_2_out1 : Unsigned_16;
      Sum1_out1 : Integer_32;
      Sum1_1_out1 : Integer_32;
      Sum2_out1 : Integer_32;
      Sum2_1_out1 : Integer_32;
      Sum1_1_1_out1 : Integer_32;
      Sum_out1 : Integer_32;
      Sum2_2_out1 : Integer_32;
      Compare_To_Constant_out1 : Boolean;
      Sum_1_out1 : Integer_32;
      Sum_2_out1 : Integer_32;
      Sum_3_out1 : Integer_32;
      Left_out1 : Integer_32;
      Left_1_out1 : Integer_32;
      Left_2_out1 : Integer_32;
      To_uint16_Result_out1 : Unsigned_16;
      To_uint16_Result_1_out1 : Unsigned_16;
      To_uint16_Result_2_out1 : Unsigned_16;
      Distance_km_out1 : Long_Float;
      Elapsed_Time_h_out1 : Long_Float;
      Relational_Operator_out1 : Boolean;
      Avoid_Div_by_Zero_out1 : Long_Float;
      Relational_Operator_out1_1 : Boolean;
      Speed_out1 : Long_Float;
      Old_output_if_new_invalid_out1 : Long_Float;
   begin
      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Old NGClickTime>
      Old_NGClickTime_out1 := Old_NGClickTime_memory;
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Old NGClickTime>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Old NGRotations>
      Old_NGRotations_out1 := Old_NGRotations_memory;
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Old NGRotations>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Old estimatedGroundVelocity>
      Old_estimatedGroundVelocity_out1 := Old_estimatedGroundVelocity_memory;
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Old estimatedGroundVelocity>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Rotations/Max uint16>
      Max_uint16_out1 := 65535;
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Rotations/Max uint16>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Time/Max uint16>
      Max_uint16_1_out1 := 65535;
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Time/Max uint16>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Age of oldest time/Max uint16>
      Max_uint16_2_out1 := 65535;
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Age of oldest time/Max uint16>

      --  Block: <INTERFACE_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Millisecs>
      Millisecs_out1 := Millisecs;
      --  End Block: <INTERFACE_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Millisecs>

      --  Block: <INTERFACE_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/NGClickTime>
      NGClickTime_out1 := NGClickTime;
      --  End Block: <INTERFACE_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/NGClickTime>

      --  Block: <INTERFACE_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/NGRotations>
      NGRotations_out1 := NGRotations;
      --  End Block: <INTERFACE_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/NGRotations>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Wheel Circunference>
      Wheel_Circunference_out1 := (nose_gear_params.PI) * (nose_gear_params.WHEEL_DIAMETER);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Wheel Circunference>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/ms in hour>
      ms_in_hour_out1 := (3600.0) * (1000.0);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/ms in hour>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/ms in our1>
      ms_in_our1_out1 := 1.0;
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/ms in our1>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Update Period\n(OS interrupt)>
      Update_Period_OS_interrupt_out1 := Unsigned_16 (nose_gear_params.UPDATE_PERIOD);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Update Period\n(OS interrupt)>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Validity Period>
      Validity_Period_out1 := Unsigned_16 (nose_gear_params.VALIDITY_PERIOD);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Validity Period>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Rotations/To_int32_Left>
      To_int32_Left_out1 := Integer_32 (NGRotations_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Rotations/To_int32_Left>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Time/To_int32_Left>
      To_int32_Left_1_out1 := Integer_32 (NGClickTime_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Time/To_int32_Left>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Age of oldest time/To_int32_Left>
      To_int32_Left_2_out1 := Integer_32 (Millisecs_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Age of oldest time/To_int32_Left>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Rotations/To_int32_Right>
      To_int32_Right_out1 := Integer_32 (Old_NGRotations_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Rotations/To_int32_Right>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Time/To_int32_Right>
      To_int32_Right_1_out1 := Integer_32 (Old_NGClickTime_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Time/To_int32_Right>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Age of oldest time/To_int32_Right>
      To_int32_Right_2_out1 := Integer_32 (Old_NGClickTime_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Age of oldest time/To_int32_Right>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/CheckContract/Data Type Conversion1>
      Data_Type_Conversion1_out1 := Integer_32 (Millisecs_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/CheckContract/Data Type Conversion1>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/CheckContract/Data Type Conversion>
      Data_Type_Conversion_out1 := Integer_32 (Old_NGClickTime_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/CheckContract/Data Type Conversion>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Sum1>
      Sum1_2_out1 := (Validity_Period_out1) - (Update_Period_OS_interrupt_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Sum1>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Rotations/Sum1>
      Sum1_out1 := (To_int32_Right_out1) - (To_int32_Left_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Rotations/Sum1>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Time/Sum1>
      Sum1_1_out1 := (To_int32_Right_1_out1) - (To_int32_Left_1_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Time/Sum1>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Rotations/Sum2>
      Sum2_out1 := (To_int32_Left_out1) - (To_int32_Right_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Rotations/Sum2>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Time/Sum2>
      Sum2_1_out1 := (To_int32_Left_1_out1) - (To_int32_Right_1_out1);
      -- pragma assert (Sum2_1_out1 <= Integer_32(Unsigned_16'Last));
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Time/Sum2>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Age of oldest time/Sum1>
      Sum1_1_1_out1 := (To_int32_Right_2_out1) - (To_int32_Left_2_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Age of oldest time/Sum1>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/CheckContract/Sum>
      Sum_out1 := (Data_Type_Conversion1_out1) - (Data_Type_Conversion_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/CheckContract/Sum>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Age of oldest time/Sum2>
      Sum2_2_out1 := (To_int32_Left_2_out1) - (To_int32_Right_2_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Age of oldest time/Sum2>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/CheckContract/Compare To Constant>
      Compare_To_Constant_out1 := (Long_Float (Sum_out1)) <= (nose_gear_params.VALIDITY_PERIOD);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/CheckContract/Compare To Constant>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Rotations/Sum>
      Sum_1_out1 := (Max_uint16_out1) - (Sum1_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Rotations/Sum>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Time/Sum>
      Sum_2_out1 := (Max_uint16_1_out1) - (Sum1_1_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Time/Sum>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Age of oldest time/Sum>
      Sum_3_out1 := (Max_uint16_2_out1) - (Sum1_1_1_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Age of oldest time/Sum>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Rotations/Left>

      if (Sum2_out1) >= (0) then
         Left_out1 := Sum2_out1;
      else
         Left_out1 := Sum_1_out1;
      end if;

      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Rotations/Left>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Time/Left>

      if (Sum2_1_out1) >= (0) then
         Left_1_out1 := Sum2_1_out1;
         -- pragma assert (Sum2_1_out1 <= Integer_32(Unsigned_16'Last));
      else
         Left_1_out1 := Sum_2_out1;
         -- pragma assert (Left_1_out1 <= Integer_32(Unsigned_16'Last));
      end if;

      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Time/Left>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Age of oldest time/Left>

      if (Sum2_2_out1) >= (0) then
         Left_2_out1 := Sum2_2_out1;
      else
         Left_2_out1 := Sum_3_out1;
      end if;

      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Age of oldest time/Left>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Rotations/To_uint16_Result>
      To_uint16_Result_out1 := Unsigned_16 (Left_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Rotations/To_uint16_Result>

      pragma assert (Left_1_out1 <= Integer_32(Unsigned_16'Last));
      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Time/To_uint16_Result>
      To_uint16_Result_1_out1 := Unsigned_16 (Left_1_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Substract Time/To_uint16_Result>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Age of oldest time/To_uint16_Result>
      To_uint16_Result_2_out1 := Unsigned_16 (Left_2_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Age of oldest time/To_uint16_Result>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Distance (km)>
      Distance_km_out1 := (Long_Float (To_uint16_Result_out1)) * (Wheel_Circunference_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Distance (km)>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Elapsed Time (h)>
      Elapsed_Time_h_out1 := (Long_Float (To_uint16_Result_1_out1)) / (ms_in_hour_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Elapsed Time (h)>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Relational\nOperator>
      Relational_Operator_out1 := (To_uint16_Result_2_out1) <= (Sum1_2_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Validity Check/Relational\nOperator>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Avoid Div by Zero>

      if (To_uint16_Result_1_out1) > (0) then
         Avoid_Div_by_Zero_out1 := Elapsed_Time_h_out1;
      else
         Avoid_Div_by_Zero_out1 := ms_in_our1_out1;
      end if;

      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Avoid Div by Zero>

      --  Block: <INTERFACE_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/estimatedGroundVelocityIsAvailable>
      estimatedGroundVelocityIsAvailable := Relational_Operator_out1;
      --  End Block: <INTERFACE_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/estimatedGroundVelocityIsAvailable>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/CheckContract/Relational Operator>
      Relational_Operator_out1_1 := (Relational_Operator_out1) = (Compare_To_Constant_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/CheckContract/Relational Operator>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Speed>
      Speed_out1 := (Distance_km_out1) / (Avoid_Div_by_Zero_out1);
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Speed>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/CheckContract/Assertion>
      -- pragma Assert (Relational_Operator_out1_1, "Violation of assertion at block nose_gear/Estimate Ground Velocity/CheckContract/Assertion");
      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/CheckContract/Assertion>

      --  Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Old output if new invalid>

      if Relational_Operator_out1 then
         Old_output_if_new_invalid_out1 := Speed_out1;
      else
         Old_output_if_new_invalid_out1 := Old_estimatedGroundVelocity_out1;
      end if;

      --  End Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Old output if new invalid>

      --  Block: <INTERFACE_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/estimatedGroundVelocity>
      estimatedGroundVelocity := Old_output_if_new_invalid_out1;
      --  End Block: <INTERFACE_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/estimatedGroundVelocity>

      --  Memory update of Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Old estimatedGroundVelocity>
      Old_estimatedGroundVelocity_memory := Old_output_if_new_invalid_out1;
      --  End Memory update of Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Old estimatedGroundVelocity>

      --  Memory update of Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Old NGRotations>
      Old_NGRotations_memory := NGRotations_out1;
      --  End Memory update of Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Old NGRotations>

      --  Memory update of Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Old NGClickTime>
      Old_NGClickTime_memory := NGClickTime_out1;
      --  End Memory update of Block: <ELEMENTARY_BLOCK_META originalFullName=nose_gear/Estimate Ground Velocity/Old NGClickTime>
   end nose_gear_comp;
end nose_gear;
--  @EOF

