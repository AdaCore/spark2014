--  Copyright (C) Your Company Name
--
--  @generated with QGen Code Generator 2.0.0w (20150420)
--  Command line arguments:
--    --clean models/case_studies/NASA-DO-333-Case-Studies/Mode_Logic_Case_Study_Files/Mode_Logic_Props.mdl
--    --output models/case_studies/NASA-DO-333-Case-Studies/Mode_Logic_Case_Study_Files/Mode_Logic_Props/hmc_ada
--    --language ada
--    --debug
--    --typing models/case_studies/NASA-DO-333-Case-Studies/Mode_Logic_Case_Study_Files/Mode_Logic_Props_types.txt

pragma Style_Checks ("M999");  --  ignore long lines

package body Flight_Modes is
   C2_Active : Boolean;
   C2_FD_Active : Boolean;
   C2_FD_ON_Active : Boolean;
   C2_FD_OFF_Active : Boolean;
   C2_ANNUNCIATIONS_Active : Boolean;
   C2_ANNUNCIATIONS_ON_Active : Boolean;
   C2_ANNUNCIATIONS_OFF_Active : Boolean;
   C2_INDEPENDENT_Active : Boolean;
   C2_INDEPENDENT_INDEPENDENT_Active : Boolean;
   C2_INDEPENDENT_DEPENDENT_Active : Boolean;
   C2_ACTIVE_Active : Boolean;
   C2_ACTIVE_ACTIVE_Active : Boolean;
   C2_ACTIVE_INACTIVE_Active : Boolean;
   C2_LATERAL_Active : Boolean;
   C2_LATERAL_HDG_Active : Boolean;
   C2_LATERAL_HDG_SELECTED_Active : Boolean;
   C2_LATERAL_HDG_SELECTED_ACTIVE_Active : Boolean;
   C2_LATERAL_HDG_CLEARED_Active : Boolean;
   C2_LATERAL_NAV_Active : Boolean;
   C2_LATERAL_NAV_SELECTED_Active : Boolean;
   C2_LATERAL_NAV_SELECTED_ACTIVE_Active : Boolean;
   C2_LATERAL_NAV_SELECTED_ARMED_Active : Boolean;
   C2_LATERAL_NAV_CLEARED_Active : Boolean;
   C2_LATERAL_LAPPR_Active : Boolean;
   C2_LATERAL_LAPPR_SELECTED_Active : Boolean;
   C2_LATERAL_LAPPR_SELECTED_ACTIVE_Active : Boolean;
   C2_LATERAL_LAPPR_SELECTED_ARMED_Active : Boolean;
   C2_LATERAL_LAPPR_CLEARED_Active : Boolean;
   C2_LATERAL_LGA_Active : Boolean;
   C2_LATERAL_LGA_SELECTED_Active : Boolean;
   C2_LATERAL_LGA_SELECTED_ACTIVE_Active : Boolean;
   C2_LATERAL_LGA_CLEARED_Active : Boolean;
   C2_LATERAL_ROLL_Active : Boolean;
   C2_LATERAL_ROLL_SELECTED_Active : Boolean;
   C2_LATERAL_ROLL_SELECTED_ACTIVE_Active : Boolean;
   C2_LATERAL_ROLL_CLEARED_Active : Boolean;
   C2_LATERAL_HDG_Will_Be_Activated : Boolean;
   C2_LATERAL_NAV_Will_Be_Activated : Boolean;
   C2_LATERAL_LAPPR_Will_Be_Activated : Boolean;
   C2_LATERAL_LGA_Will_Be_Activated : Boolean;
   C2_VERTICAL_Active : Boolean;
   C2_VERTICAL_VS_Active : Boolean;
   C2_VERTICAL_VS_SELECTED_Active : Boolean;
   C2_VERTICAL_VS_SELECTED_ACTIVE_Active : Boolean;
   C2_VERTICAL_VS_CLEARED_Active : Boolean;
   C2_VERTICAL_FLC_Active : Boolean;
   C2_VERTICAL_FLC_SELECTED_Active : Boolean;
   C2_VERTICAL_FLC_SELECTED_ACTIVE_Active : Boolean;
   C2_VERTICAL_FLC_CLEARED_Active : Boolean;
   C2_VERTICAL_ALT_Active : Boolean;
   C2_VERTICAL_ALT_SELECTED_Active : Boolean;
   C2_VERTICAL_ALT_SELECTED_ACTIVE_Active : Boolean;
   C2_VERTICAL_ALT_CLEARED_Active : Boolean;
   C2_VERTICAL_VAPPR_Active : Boolean;
   C2_VERTICAL_VAPPR_SELECTED_Active : Boolean;
   C2_VERTICAL_VAPPR_SELECTED_ACTIVE_Active : Boolean;
   C2_VERTICAL_VAPPR_SELECTED_ARMED_Active : Boolean;
   C2_VERTICAL_VAPPR_CLEARED_Active : Boolean;
   C2_VERTICAL_VGA_Active : Boolean;
   C2_VERTICAL_VGA_SELECTED_Active : Boolean;
   C2_VERTICAL_VGA_SELECTED_ACTIVE_Active : Boolean;
   C2_VERTICAL_VGA_CLEARED_Active : Boolean;
   C2_VERTICAL_ALTSEL_Active : Boolean;
   C2_VERTICAL_ALTSEL_SELECTED_Active : Boolean;
   C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_Active : Boolean;
   C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_CAPTURE_Active : Boolean;
   C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_TRACK_Active : Boolean;
   C2_VERTICAL_ALTSEL_SELECTED_ARMED_Active : Boolean;
   C2_VERTICAL_ALTSEL_CLEARED_Active : Boolean;
   C2_VERTICAL_PITCH_Active : Boolean;
   C2_VERTICAL_PITCH_SELECTED_Active : Boolean;
   C2_VERTICAL_PITCH_SELECTED_ACTIVE_Active : Boolean;
   C2_VERTICAL_PITCH_CLEARED_Active : Boolean;
   C2_VERTICAL_VS_Will_Be_Activated : Boolean;
   C2_VERTICAL_FLC_Will_Be_Activated : Boolean;
   C2_VERTICAL_ALT_Will_Be_Activated : Boolean;
   C2_VERTICAL_ALTSEL_Will_Be_Activated : Boolean;
   C2_VERTICAL_VAPPR_Will_Be_Activated : Boolean;
   C2_VERTICAL_VGA_Will_Be_Activated : Boolean;
   C2_Pilot_Flying_Side : Boolean;
   C2_Is_AP_Engaged : Boolean;
   C2_Overspeed : Boolean;
   C2_Is_Offside_FD_On : Boolean;
   C2_Is_Offside_VAPPR_Active : Boolean;
   C2_Is_Offside_VGA_Active : Boolean;
   C2_Pilot_Flying_Transfer : Boolean;
   C2_When_AP_Engaged : Boolean;
   C2_SYNC_Switch_Pressed : Boolean;
   C2_FD_Switch_Pressed : Boolean;
   C2_HDG_Switch_Pressed : Boolean;
   C2_NAV_Switch_Pressed : Boolean;
   C2_APPR_Switch_Pressed : Boolean;
   C2_GA_Switch_Pressed : Boolean;
   C2_VS_Switch_Pressed : Boolean;
   C2_FLC_Switch_Pressed : Boolean;
   C2_ALT_Switch_Pressed : Boolean;
   C2_VS_Pitch_Wheel_Rotated : Boolean;
   C2_ALTSEL_Target_Changed : Boolean;
   C2_NAV_Capture_Condition_Met : Boolean;
   C2_LAPPR_Capture_Condition_Met : Boolean;
   C2_ALTSEL_Capture_Condition_Met : Boolean;
   C2_ALTSEL_Track_Condition_Met : Boolean;
   C2_VAPPR_Capture_Condition_Met : Boolean;
   C2_Selected_NAV_Source_Changed : Boolean;
   C2_Selected_NAV_Frequency_Changed : Boolean;
   C2_Modes_On : Boolean;
   C2_FD_On : Boolean;
   C2_Independent_Mode : Boolean;
   C2_Active_Side : Boolean;
   C2_ROLL_Selected : Boolean;
   C2_ROLL_Active : Boolean;
   C2_HDG_Selected : Boolean;
   C2_HDG_Active : Boolean;
   C2_NAV_Selected : Boolean;
   C2_NAV_Active : Boolean;
   C2_LAPPR_Selected : Boolean;
   C2_LAPPR_Active : Boolean;
   C2_LGA_Selected : Boolean;
   C2_LGA_Active : Boolean;
   C2_PITCH_Selected : Boolean;
   C2_PITCH_Active : Boolean;
   C2_VS_Selected : Boolean;
   C2_VS_Active : Boolean;
   C2_FLC_Selected : Boolean;
   C2_FLC_Active : Boolean;
   C2_ALT_Selected : Boolean;
   C2_ALT_Active : Boolean;
   C2_ALTSEL_Selected : Boolean;
   C2_ALTSEL_Active : Boolean;
   C2_ALTSEL_Track : Boolean;
   C2_VAPPR_Selected : Boolean;
   C2_VAPPR_Active : Boolean;
   C2_VGA_Selected : Boolean;
   C2_VGA_Active : Boolean;

   function FD_Turn_FD_On return Boolean;

   function FD_Turn_FD_Off return Boolean;

   function FD_Lateral_Mode_Manually_Selected return Boolean;

   function FD_Vertical_Mode_Manually_Selected return Boolean;

   function ANNUNCIATIONS_Turn_Annunciations_On return Boolean;

   function ANNUNCIATIONS_Turn_Annunciations_Off return Boolean;

   function INDEPENDENT_In_Independent_Mode return Boolean;

   function ACTIVE_In_Active_Mode return Boolean;

   function LATERAL_HDG_Select return Boolean;

   function LATERAL_HDG_Clear return Boolean;

   function LATERAL_HDG_Will_Be_Activated return Boolean;

   function LATERAL_NAV_Select return Boolean;

   function LATERAL_NAV_Capture return Boolean;

   function LATERAL_NAV_Clear return Boolean;

   function LATERAL_NAV_Will_Be_Activated return Boolean;

   function LATERAL_LAPPR_Select return Boolean;

   function LATERAL_LAPPR_Capture return Boolean;

   function LATERAL_LAPPR_Clear return Boolean;

   function LATERAL_LAPPR_Will_Be_Activated return Boolean;

   function LATERAL_LGA_Select return Boolean;

   function LATERAL_LGA_Clear return Boolean;

   function LATERAL_LGA_Will_Be_Activated return Boolean;

   procedure LATERAL_Update_Activated_Modes;

   function LATERAL_Lateral_Mode_Active return Boolean;

   function LATERAL_New_Lateral_Mode_Activated return Boolean;

   function VERTICAL_VS_Select return Boolean;

   function VERTICAL_VS_Clear return Boolean;

   function VERTICAL_VS_Will_Be_Activated return Boolean;

   function VERTICAL_FLC_Select return Boolean;

   function VERTICAL_FLC_Clear return Boolean;

   function VERTICAL_FLC_Will_Be_Activated return Boolean;

   function VERTICAL_ALT_Select return Boolean;

   function VERTICAL_ALT_Clear return Boolean;

   function VERTICAL_ALT_Will_Be_Activated return Boolean;

   function VERTICAL_VAPPR_Select return Boolean;

   function VERTICAL_VAPPR_Capture return Boolean;

   function VERTICAL_VAPPR_Clear return Boolean;

   function VERTICAL_VAPPR_Will_Be_Activated return Boolean;

   function VERTICAL_VGA_Select return Boolean;

   function VERTICAL_VGA_Clear return Boolean;

   function VERTICAL_VGA_Will_Be_Activated return Boolean;

   function VERTICAL_ALTSEL_Select return Boolean;

   function VERTICAL_ALTSEL_Capture return Boolean;

   function VERTICAL_ALTSEL_Track return Boolean;

   function VERTICAL_ALTSEL_Deactivate return Boolean;

   function VERTICAL_ALTSEL_Clear return Boolean;

   function VERTICAL_ALTSEL_Will_Be_Activated return Boolean;

   procedure VERTICAL_Update_Activated_Modes;

   function VERTICAL_New_Vertical_Mode_Activated return Boolean;

   function VERTICAL_Vertical_Mode_Active return Boolean;

   procedure initStates is
   begin
      C2_Active := False;
      C2_FD_Active := False;
      C2_FD_ON_Active := False;
      C2_FD_OFF_Active := False;
      C2_ANNUNCIATIONS_Active := False;
      C2_ANNUNCIATIONS_ON_Active := False;
      C2_ANNUNCIATIONS_OFF_Active := False;
      C2_INDEPENDENT_Active := False;
      C2_INDEPENDENT_INDEPENDENT_Active := False;
      C2_INDEPENDENT_DEPENDENT_Active := False;
      C2_ACTIVE_Active := False;
      C2_ACTIVE_ACTIVE_Active := False;
      C2_ACTIVE_INACTIVE_Active := False;
      C2_LATERAL_Active := False;
      C2_LATERAL_HDG_Active := False;
      C2_LATERAL_HDG_SELECTED_Active := False;
      C2_LATERAL_HDG_SELECTED_ACTIVE_Active := False;
      C2_LATERAL_HDG_CLEARED_Active := False;
      C2_LATERAL_NAV_Active := False;
      C2_LATERAL_NAV_SELECTED_Active := False;
      C2_LATERAL_NAV_SELECTED_ACTIVE_Active := False;
      C2_LATERAL_NAV_SELECTED_ARMED_Active := False;
      C2_LATERAL_NAV_CLEARED_Active := False;
      C2_LATERAL_LAPPR_Active := False;
      C2_LATERAL_LAPPR_SELECTED_Active := False;
      C2_LATERAL_LAPPR_SELECTED_ACTIVE_Active := False;
      C2_LATERAL_LAPPR_SELECTED_ARMED_Active := False;
      C2_LATERAL_LAPPR_CLEARED_Active := False;
      C2_LATERAL_LGA_Active := False;
      C2_LATERAL_LGA_SELECTED_Active := False;
      C2_LATERAL_LGA_SELECTED_ACTIVE_Active := False;
      C2_LATERAL_LGA_CLEARED_Active := False;
      C2_LATERAL_ROLL_Active := False;
      C2_LATERAL_ROLL_SELECTED_Active := False;
      C2_LATERAL_ROLL_SELECTED_ACTIVE_Active := False;
      C2_LATERAL_ROLL_CLEARED_Active := False;
      C2_VERTICAL_Active := False;
      C2_VERTICAL_VS_Active := False;
      C2_VERTICAL_VS_SELECTED_Active := False;
      C2_VERTICAL_VS_SELECTED_ACTIVE_Active := False;
      C2_VERTICAL_VS_CLEARED_Active := False;
      C2_VERTICAL_FLC_Active := False;
      C2_VERTICAL_FLC_SELECTED_Active := False;
      C2_VERTICAL_FLC_SELECTED_ACTIVE_Active := False;
      C2_VERTICAL_FLC_CLEARED_Active := False;
      C2_VERTICAL_ALT_Active := False;
      C2_VERTICAL_ALT_SELECTED_Active := False;
      C2_VERTICAL_ALT_SELECTED_ACTIVE_Active := False;
      C2_VERTICAL_ALT_CLEARED_Active := False;
      C2_VERTICAL_VAPPR_Active := False;
      C2_VERTICAL_VAPPR_SELECTED_Active := False;
      C2_VERTICAL_VAPPR_SELECTED_ACTIVE_Active := False;
      C2_VERTICAL_VAPPR_SELECTED_ARMED_Active := False;
      C2_VERTICAL_VAPPR_CLEARED_Active := False;
      C2_VERTICAL_VGA_Active := False;
      C2_VERTICAL_VGA_SELECTED_Active := False;
      C2_VERTICAL_VGA_SELECTED_ACTIVE_Active := False;
      C2_VERTICAL_VGA_CLEARED_Active := False;
      C2_VERTICAL_ALTSEL_Active := False;
      C2_VERTICAL_ALTSEL_SELECTED_Active := False;
      C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_Active := False;
      C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_CAPTURE_Active := False;
      C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_TRACK_Active := False;
      C2_VERTICAL_ALTSEL_SELECTED_ARMED_Active := False;
      C2_VERTICAL_ALTSEL_CLEARED_Active := False;
      C2_VERTICAL_PITCH_Active := False;
      C2_VERTICAL_PITCH_SELECTED_Active := False;
      C2_VERTICAL_PITCH_SELECTED_ACTIVE_Active := False;
      C2_VERTICAL_PITCH_CLEARED_Active := False;
      C2_Modes_On := False;
      C2_FD_On := False;
      C2_Independent_Mode := False;
      C2_Active_Side := False;
      C2_ROLL_Selected := False;
      C2_ROLL_Active := False;
      C2_HDG_Selected := False;
      C2_HDG_Active := False;
      C2_NAV_Selected := False;
      C2_NAV_Active := False;
      C2_LAPPR_Selected := False;
      C2_LAPPR_Active := False;
      C2_LGA_Selected := False;
      C2_LGA_Active := False;
      C2_PITCH_Selected := False;
      C2_PITCH_Active := False;
      C2_VS_Selected := False;
      C2_VS_Active := False;
      C2_FLC_Selected := False;
      C2_FLC_Active := False;
      C2_ALT_Selected := False;
      C2_ALT_Active := False;
      C2_ALTSEL_Selected := False;
      C2_ALTSEL_Active := False;
      C2_ALTSEL_Track := False;
      C2_VAPPR_Selected := False;
      C2_VAPPR_Active := False;
      C2_VGA_Selected := False;
      C2_VGA_Active := False;
   end initStates;

   procedure initOutputs
      (Modes_On : out Boolean;
       FD_On : out Boolean;
       Independent_Mode : out Boolean;
       Active_Side : out Boolean;
       ROLL_Selected : out Boolean;
       ROLL_Active : out Boolean;
       HDG_Selected : out Boolean;
       HDG_Active : out Boolean;
       NAV_Selected : out Boolean;
       NAV_Active : out Boolean;
       LAPPR_Selected : out Boolean;
       LAPPR_Active : out Boolean;
       LGA_Selected : out Boolean;
       LGA_Active : out Boolean;
       PITCH_Selected : out Boolean;
       PITCH_Active : out Boolean;
       VS_Selected : out Boolean;
       VS_Active : out Boolean;
       FLC_Selected : out Boolean;
       FLC_Active : out Boolean;
       ALT_Selected : out Boolean;
       ALT_Active : out Boolean;
       ALTSEL_Selected : out Boolean;
       ALTSEL_Active : out Boolean;
       ALTSEL_Track : out Boolean;
       VAPPR_Selected : out Boolean;
       VAPPR_Active : out Boolean;
       VGA_Selected : out Boolean;
       VGA_Active : out Boolean)
   is
      use type Boolean;
   begin
      Modes_On := C2_Modes_On;
      FD_On := C2_FD_On;
      Independent_Mode := C2_Independent_Mode;
      Active_Side := C2_Active_Side;
      ROLL_Selected := C2_ROLL_Selected;
      ROLL_Active := C2_ROLL_Active;
      HDG_Selected := C2_HDG_Selected;
      HDG_Active := C2_HDG_Active;
      NAV_Selected := C2_NAV_Selected;
      NAV_Active := C2_NAV_Active;
      LAPPR_Selected := C2_LAPPR_Selected;
      LAPPR_Active := C2_LAPPR_Active;
      LGA_Selected := C2_LGA_Selected;
      LGA_Active := C2_LGA_Active;
      PITCH_Selected := C2_PITCH_Selected;
      PITCH_Active := C2_PITCH_Active;
      VS_Selected := C2_VS_Selected;
      VS_Active := C2_VS_Active;
      FLC_Selected := C2_FLC_Selected;
      FLC_Active := C2_FLC_Active;
      ALT_Selected := C2_ALT_Selected;
      ALT_Active := C2_ALT_Active;
      ALTSEL_Selected := C2_ALTSEL_Selected;
      ALTSEL_Active := C2_ALTSEL_Active;
      ALTSEL_Track := C2_ALTSEL_Track;
      VAPPR_Selected := C2_VAPPR_Selected;
      VAPPR_Active := C2_VAPPR_Active;
      VGA_Selected := C2_VGA_Selected;
      VGA_Active := C2_VGA_Active;
   end initOutputs;

   procedure comp
      (Pilot_Flying_Side : Boolean;
       Is_AP_Engaged : Boolean;
       Overspeed : Boolean;
       Is_Offside_FD_On : Boolean;
       Is_Offside_VAPPR_Active : Boolean;
       Is_Offside_VGA_Active : Boolean;
       Pilot_Flying_Transfer : Boolean;
       When_AP_Engaged : Boolean;
       SYNC_Switch_Pressed : Boolean;
       FD_Switch_Pressed : Boolean;
       HDG_Switch_Pressed : Boolean;
       NAV_Switch_Pressed : Boolean;
       APPR_Switch_Pressed : Boolean;
       GA_Switch_Pressed : Boolean;
       VS_Switch_Pressed : Boolean;
       FLC_Switch_Pressed : Boolean;
       ALT_Switch_Pressed : Boolean;
       VS_Pitch_Wheel_Rotated : Boolean;
       ALTSEL_Target_Changed : Boolean;
       NAV_Capture_Condition_Met : Boolean;
       LAPPR_Capture_Condition_Met : Boolean;
       ALTSEL_Capture_Condition_Met : Boolean;
       ALTSEL_Track_Condition_Met : Boolean;
       VAPPR_Capture_Condition_Met : Boolean;
       Selected_NAV_Source_Changed : Boolean;
       Selected_NAV_Frequency_Changed : Boolean;
       Modes_On : out Boolean;
       FD_On : out Boolean;
       Independent_Mode : out Boolean;
       Active_Side : out Boolean;
       ROLL_Selected : out Boolean;
       ROLL_Active : out Boolean;
       HDG_Selected : out Boolean;
       HDG_Active : out Boolean;
       NAV_Selected : out Boolean;
       NAV_Active : out Boolean;
       LAPPR_Selected : out Boolean;
       LAPPR_Active : out Boolean;
       LGA_Selected : out Boolean;
       LGA_Active : out Boolean;
       PITCH_Selected : out Boolean;
       PITCH_Active : out Boolean;
       VS_Selected : out Boolean;
       VS_Active : out Boolean;
       FLC_Selected : out Boolean;
       FLC_Active : out Boolean;
       ALT_Selected : out Boolean;
       ALT_Active : out Boolean;
       ALTSEL_Selected : out Boolean;
       ALTSEL_Active : out Boolean;
       ALTSEL_Track : out Boolean;
       VAPPR_Selected : out Boolean;
       VAPPR_Active : out Boolean;
       VGA_Selected : out Boolean;
       VGA_Active : out Boolean)
   is
      use type Boolean;
   begin
      --  Copy inputs Mode_Logic_Props/Mode_Logic/Flight_Modes
      C2_Pilot_Flying_Side := Pilot_Flying_Side;
      C2_Is_AP_Engaged := Is_AP_Engaged;
      C2_Overspeed := Overspeed;
      C2_Is_Offside_FD_On := Is_Offside_FD_On;
      C2_Is_Offside_VAPPR_Active := Is_Offside_VAPPR_Active;
      C2_Is_Offside_VGA_Active := Is_Offside_VGA_Active;
      C2_Pilot_Flying_Transfer := Pilot_Flying_Transfer;
      C2_When_AP_Engaged := When_AP_Engaged;
      C2_SYNC_Switch_Pressed := SYNC_Switch_Pressed;
      C2_FD_Switch_Pressed := FD_Switch_Pressed;
      C2_HDG_Switch_Pressed := HDG_Switch_Pressed;
      C2_NAV_Switch_Pressed := NAV_Switch_Pressed;
      C2_APPR_Switch_Pressed := APPR_Switch_Pressed;
      C2_GA_Switch_Pressed := GA_Switch_Pressed;
      C2_VS_Switch_Pressed := VS_Switch_Pressed;
      C2_FLC_Switch_Pressed := FLC_Switch_Pressed;
      C2_ALT_Switch_Pressed := ALT_Switch_Pressed;
      C2_VS_Pitch_Wheel_Rotated := VS_Pitch_Wheel_Rotated;
      C2_ALTSEL_Target_Changed := ALTSEL_Target_Changed;
      C2_NAV_Capture_Condition_Met := NAV_Capture_Condition_Met;
      C2_LAPPR_Capture_Condition_Met := LAPPR_Capture_Condition_Met;
      C2_ALTSEL_Capture_Condition_Met := ALTSEL_Capture_Condition_Met;
      C2_ALTSEL_Track_Condition_Met := ALTSEL_Track_Condition_Met;
      C2_VAPPR_Capture_Condition_Met := VAPPR_Capture_Condition_Met;
      C2_Selected_NAV_Source_Changed := Selected_NAV_Source_Changed;
      C2_Selected_NAV_Frequency_Changed := Selected_NAV_Frequency_Changed;

      --  Execute chart Mode_Logic_Props/Mode_Logic/Flight_Modes

      if not  (C2_Active) then

         --  Open and enter chart
         C2_Active := True;

         --  Enter state FD
         C2_FD_Active := True;

         --  Enter state OFF
         C2_FD_OFF_Active := True;

         --  Enter state ANNUNCIATIONS
         C2_ANNUNCIATIONS_Active := True;

         --  Enter state OFF
         C2_ANNUNCIATIONS_OFF_Active := True;

         --  Enter state INDEPENDENT
         C2_INDEPENDENT_Active := True;

         --  Enter state DEPENDENT
         C2_INDEPENDENT_DEPENDENT_Active := True;

         --  Enter state ACTIVE
         C2_ACTIVE_Active := True;

         --  Enter state INACTIVE
         C2_ACTIVE_INACTIVE_Active := True;

         --  Enter state LATERAL
         C2_LATERAL_Active := True;
         C2_LATERAL_HDG_Will_Be_Activated := False;
         C2_LATERAL_NAV_Will_Be_Activated := False;
         C2_LATERAL_LAPPR_Will_Be_Activated := False;
         C2_LATERAL_LGA_Will_Be_Activated := False;
         LATERAL_Update_Activated_Modes;

         --  Enter state HDG
         C2_LATERAL_HDG_Active := True;

         --  Enter state CLEARED
         C2_LATERAL_HDG_CLEARED_Active := True;

         --  Enter state NAV
         C2_LATERAL_NAV_Active := True;

         --  Enter state CLEARED
         C2_LATERAL_NAV_CLEARED_Active := True;

         --  Enter state LAPPR
         C2_LATERAL_LAPPR_Active := True;

         --  Enter state CLEARED
         C2_LATERAL_LAPPR_CLEARED_Active := True;

         --  Enter state LGA
         C2_LATERAL_LGA_Active := True;

         --  Enter state CLEARED
         C2_LATERAL_LGA_CLEARED_Active := True;

         --  Enter state ROLL
         C2_LATERAL_ROLL_Active := True;

         --  Enter state SELECTED
         C2_LATERAL_ROLL_SELECTED_Active := True;
         C2_ROLL_Selected := True;

         --  Enter state ACTIVE
         C2_LATERAL_ROLL_SELECTED_ACTIVE_Active := True;
         C2_ROLL_Active := True;

         --  Enter state VERTICAL
         C2_VERTICAL_Active := True;
         C2_VERTICAL_VS_Will_Be_Activated := False;
         C2_VERTICAL_FLC_Will_Be_Activated := False;
         C2_VERTICAL_ALT_Will_Be_Activated := False;
         C2_VERTICAL_ALTSEL_Will_Be_Activated := False;
         C2_VERTICAL_VAPPR_Will_Be_Activated := False;
         C2_VERTICAL_VGA_Will_Be_Activated := False;
         VERTICAL_Update_Activated_Modes;

         --  Enter state VS
         C2_VERTICAL_VS_Active := True;

         --  Enter state CLEARED
         C2_VERTICAL_VS_CLEARED_Active := True;

         --  Enter state FLC
         C2_VERTICAL_FLC_Active := True;

         --  Enter state CLEARED
         C2_VERTICAL_FLC_CLEARED_Active := True;

         --  Enter state ALT
         C2_VERTICAL_ALT_Active := True;

         --  Enter state CLEARED
         C2_VERTICAL_ALT_CLEARED_Active := True;

         --  Enter state VAPPR
         C2_VERTICAL_VAPPR_Active := True;

         --  Enter state CLEARED
         C2_VERTICAL_VAPPR_CLEARED_Active := True;

         --  Enter state VGA
         C2_VERTICAL_VGA_Active := True;

         --  Enter state CLEARED
         C2_VERTICAL_VGA_CLEARED_Active := True;

         --  Enter state ALTSEL
         C2_VERTICAL_ALTSEL_Active := True;

         --  Enter state SELECTED
         C2_VERTICAL_ALTSEL_SELECTED_Active := True;
         C2_ALTSEL_Selected := True;

         --  Enter state ARMED
         C2_VERTICAL_ALTSEL_SELECTED_ARMED_Active := True;

         --  Enter state PITCH
         C2_VERTICAL_PITCH_Active := True;

         --  Enter state SELECTED
         C2_VERTICAL_PITCH_SELECTED_Active := True;
         C2_PITCH_Selected := True;

         --  Enter state ACTIVE
         C2_VERTICAL_PITCH_SELECTED_ACTIVE_Active := True;
         C2_PITCH_Active := True;
      else

         --  Execute open chart

         if C2_FD_ON_Active then

            if FD_Turn_FD_Off then

               --  Exit state ON
               C2_FD_On := False;
               C2_FD_ON_Active := False;

               --  Enter state OFF
               C2_FD_OFF_Active := True;
            end if;

         else

            if C2_FD_OFF_Active then

               if FD_Turn_FD_On then

                  --  Exit state OFF
                  C2_FD_OFF_Active := False;

                  --  Enter state ON
                  C2_FD_ON_Active := True;
                  C2_FD_On := True;
               end if;

            end if;

         end if;

         if C2_ANNUNCIATIONS_ON_Active then

            if ANNUNCIATIONS_Turn_Annunciations_Off then

               --  Exit state ON
               C2_Modes_On := False;
               C2_ANNUNCIATIONS_ON_Active := False;

               --  Enter state OFF
               C2_ANNUNCIATIONS_OFF_Active := True;
            end if;

         else

            if C2_ANNUNCIATIONS_OFF_Active then

               if ANNUNCIATIONS_Turn_Annunciations_On then

                  --  Exit state OFF
                  C2_ANNUNCIATIONS_OFF_Active := False;

                  --  Enter state ON
                  C2_ANNUNCIATIONS_ON_Active := True;
                  C2_Modes_On := True;
               end if;

            end if;

         end if;

         if C2_INDEPENDENT_INDEPENDENT_Active then

            if not  (INDEPENDENT_In_Independent_Mode) then

               --  Exit state INDEPENDENT
               C2_Independent_Mode := False;
               C2_INDEPENDENT_INDEPENDENT_Active := False;

               --  Enter state DEPENDENT
               C2_INDEPENDENT_DEPENDENT_Active := True;
            end if;

         else

            if C2_INDEPENDENT_DEPENDENT_Active then

               if INDEPENDENT_In_Independent_Mode then

                  --  Exit state DEPENDENT
                  C2_INDEPENDENT_DEPENDENT_Active := False;

                  --  Enter state INDEPENDENT
                  C2_INDEPENDENT_INDEPENDENT_Active := True;
                  C2_Independent_Mode := True;
               end if;

            end if;

         end if;

         if C2_ACTIVE_ACTIVE_Active then

            if not  (ACTIVE_In_Active_Mode) then

               --  Exit state ACTIVE
               C2_Active_Side := False;
               C2_ACTIVE_ACTIVE_Active := False;

               --  Enter state INACTIVE
               C2_ACTIVE_INACTIVE_Active := True;
            end if;

         else

            if C2_ACTIVE_INACTIVE_Active then

               if ACTIVE_In_Active_Mode then

                  --  Exit state INACTIVE
                  C2_ACTIVE_INACTIVE_Active := False;

                  --  Enter state ACTIVE
                  C2_ACTIVE_ACTIVE_Active := True;
                  C2_Active_Side := True;
               end if;

            end if;

         end if;

         --  Execute state LATERAL
         LATERAL_Update_Activated_Modes;

         if C2_LATERAL_HDG_SELECTED_Active then

            if LATERAL_HDG_Clear then

               --  Exit state SELECTED

               --  Close the inner composition of state SELECTED

               if C2_LATERAL_HDG_SELECTED_ACTIVE_Active then

                  --  Exit state ACTIVE
                  C2_HDG_Active := False;
                  C2_LATERAL_HDG_SELECTED_ACTIVE_Active := False;
               end if;

               C2_HDG_Selected := False;
               C2_LATERAL_HDG_SELECTED_Active := False;

               --  Enter state CLEARED
               C2_LATERAL_HDG_CLEARED_Active := True;
            else

               if C2_LATERAL_HDG_SELECTED_ACTIVE_Active then

                  if LATERAL_New_Lateral_Mode_Activated then

                     --  Exit state ACTIVE
                     C2_HDG_Active := False;

                     --  Exit state SELECTED
                     C2_HDG_Selected := False;
                     C2_LATERAL_HDG_SELECTED_Active := False;
                     C2_LATERAL_HDG_SELECTED_ACTIVE_Active := False;

                     --  Enter state CLEARED
                     C2_LATERAL_HDG_CLEARED_Active := True;
                  end if;

               end if;

            end if;

         else

            if C2_LATERAL_HDG_CLEARED_Active then

               if LATERAL_HDG_Select then

                  --  Exit state CLEARED
                  C2_LATERAL_HDG_CLEARED_Active := False;

                  --  Enter state SELECTED
                  C2_LATERAL_HDG_SELECTED_Active := True;
                  C2_HDG_Selected := True;

                  --  Enter state ACTIVE
                  C2_LATERAL_HDG_SELECTED_ACTIVE_Active := True;
                  C2_HDG_Active := True;
               end if;

            end if;

         end if;

         if C2_LATERAL_NAV_SELECTED_Active then

            if LATERAL_NAV_Clear then

               --  Exit state SELECTED

               --  Close the inner composition of state SELECTED

               if C2_LATERAL_NAV_SELECTED_ACTIVE_Active then

                  --  Exit state ACTIVE
                  C2_NAV_Active := False;
                  C2_LATERAL_NAV_SELECTED_ACTIVE_Active := False;
               else

                  if C2_LATERAL_NAV_SELECTED_ARMED_Active then

                     --  Exit state ARMED
                     C2_LATERAL_NAV_SELECTED_ARMED_Active := False;
                  end if;

               end if;

               C2_NAV_Selected := False;
               C2_LATERAL_NAV_SELECTED_Active := False;

               --  Enter state CLEARED
               C2_LATERAL_NAV_CLEARED_Active := True;
            else

               if C2_LATERAL_NAV_SELECTED_ACTIVE_Active then

                  if LATERAL_New_Lateral_Mode_Activated then

                     --  Exit state ACTIVE
                     C2_NAV_Active := False;

                     --  Exit state SELECTED
                     C2_NAV_Selected := False;
                     C2_LATERAL_NAV_SELECTED_Active := False;
                     C2_LATERAL_NAV_SELECTED_ACTIVE_Active := False;

                     --  Enter state CLEARED
                     C2_LATERAL_NAV_CLEARED_Active := True;
                  end if;

               else

                  if C2_LATERAL_NAV_SELECTED_ARMED_Active then

                     if LATERAL_NAV_Capture then

                        --  Exit state ARMED
                        C2_LATERAL_NAV_SELECTED_ARMED_Active := False;

                        --  Enter state ACTIVE
                        C2_LATERAL_NAV_SELECTED_ACTIVE_Active := True;
                        C2_NAV_Active := True;
                     end if;

                  end if;

               end if;

            end if;

         else

            if C2_LATERAL_NAV_CLEARED_Active then

               if LATERAL_NAV_Select then

                  --  Exit state CLEARED
                  C2_LATERAL_NAV_CLEARED_Active := False;

                  --  Enter state SELECTED
                  C2_LATERAL_NAV_SELECTED_Active := True;
                  C2_NAV_Selected := True;

                  --  Enter state ARMED
                  C2_LATERAL_NAV_SELECTED_ARMED_Active := True;
               end if;

            end if;

         end if;

         if C2_LATERAL_LAPPR_SELECTED_Active then

            if LATERAL_LAPPR_Clear then

               --  Exit state SELECTED

               --  Close the inner composition of state SELECTED

               if C2_LATERAL_LAPPR_SELECTED_ACTIVE_Active then

                  --  Exit state ACTIVE
                  C2_LAPPR_Active := False;
                  C2_LATERAL_LAPPR_SELECTED_ACTIVE_Active := False;
               else

                  if C2_LATERAL_LAPPR_SELECTED_ARMED_Active then

                     --  Exit state ARMED
                     C2_LATERAL_LAPPR_SELECTED_ARMED_Active := False;
                  end if;

               end if;

               C2_LAPPR_Selected := False;
               C2_LATERAL_LAPPR_SELECTED_Active := False;

               --  Enter state CLEARED
               C2_LATERAL_LAPPR_CLEARED_Active := True;
            else

               if C2_LATERAL_LAPPR_SELECTED_ACTIVE_Active then

                  if LATERAL_New_Lateral_Mode_Activated then

                     --  Exit state ACTIVE
                     C2_LAPPR_Active := False;

                     --  Exit state SELECTED
                     C2_LAPPR_Selected := False;
                     C2_LATERAL_LAPPR_SELECTED_Active := False;
                     C2_LATERAL_LAPPR_SELECTED_ACTIVE_Active := False;

                     --  Enter state CLEARED
                     C2_LATERAL_LAPPR_CLEARED_Active := True;
                  end if;

               else

                  if C2_LATERAL_LAPPR_SELECTED_ARMED_Active then

                     if LATERAL_LAPPR_Capture then

                        --  Exit state ARMED
                        C2_LATERAL_LAPPR_SELECTED_ARMED_Active := False;

                        --  Enter state ACTIVE
                        C2_LATERAL_LAPPR_SELECTED_ACTIVE_Active := True;
                        C2_LAPPR_Active := True;
                     end if;

                  end if;

               end if;

            end if;

         else

            if C2_LATERAL_LAPPR_CLEARED_Active then

               if LATERAL_LAPPR_Select then

                  --  Exit state CLEARED
                  C2_LATERAL_LAPPR_CLEARED_Active := False;

                  --  Enter state SELECTED
                  C2_LATERAL_LAPPR_SELECTED_Active := True;
                  C2_LAPPR_Selected := True;

                  --  Enter state ARMED
                  C2_LATERAL_LAPPR_SELECTED_ARMED_Active := True;
               end if;

            end if;

         end if;

         if C2_LATERAL_LGA_SELECTED_Active then

            if LATERAL_LGA_Clear then

               --  Exit state SELECTED

               --  Close the inner composition of state SELECTED

               if C2_LATERAL_LGA_SELECTED_ACTIVE_Active then

                  --  Exit state ACTIVE
                  C2_LGA_Active := False;
                  C2_LATERAL_LGA_SELECTED_ACTIVE_Active := False;
               end if;

               C2_LGA_Selected := False;
               C2_LATERAL_LGA_SELECTED_Active := False;

               --  Enter state CLEARED
               C2_LATERAL_LGA_CLEARED_Active := True;
            else

               if C2_LATERAL_LGA_SELECTED_ACTIVE_Active then

                  if LATERAL_New_Lateral_Mode_Activated then

                     --  Exit state ACTIVE
                     C2_LGA_Active := False;

                     --  Exit state SELECTED
                     C2_LGA_Selected := False;
                     C2_LATERAL_LGA_SELECTED_Active := False;
                     C2_LATERAL_LGA_SELECTED_ACTIVE_Active := False;

                     --  Enter state CLEARED
                     C2_LATERAL_LGA_CLEARED_Active := True;
                  end if;

               end if;

            end if;

         else

            if C2_LATERAL_LGA_CLEARED_Active then

               if LATERAL_LGA_Select then

                  --  Exit state CLEARED
                  C2_LATERAL_LGA_CLEARED_Active := False;

                  --  Enter state SELECTED
                  C2_LATERAL_LGA_SELECTED_Active := True;
                  C2_LGA_Selected := True;

                  --  Enter state ACTIVE
                  C2_LATERAL_LGA_SELECTED_ACTIVE_Active := True;
                  C2_LGA_Active := True;
               end if;

            end if;

         end if;

         if C2_LATERAL_ROLL_SELECTED_Active then

            if C2_LATERAL_ROLL_SELECTED_ACTIVE_Active then

               if LATERAL_Lateral_Mode_Active then

                  --  Exit state ACTIVE
                  C2_ROLL_Active := False;

                  --  Exit state SELECTED
                  C2_ROLL_Selected := False;
                  C2_LATERAL_ROLL_SELECTED_Active := False;
                  C2_LATERAL_ROLL_SELECTED_ACTIVE_Active := False;

                  --  Enter state CLEARED
                  C2_LATERAL_ROLL_CLEARED_Active := True;
               end if;

            end if;

         else

            if C2_LATERAL_ROLL_CLEARED_Active then

               if not  (LATERAL_Lateral_Mode_Active) then

                  --  Exit state CLEARED
                  C2_LATERAL_ROLL_CLEARED_Active := False;

                  --  Enter state SELECTED
                  C2_LATERAL_ROLL_SELECTED_Active := True;
                  C2_ROLL_Selected := True;

                  --  Enter state ACTIVE
                  C2_LATERAL_ROLL_SELECTED_ACTIVE_Active := True;
                  C2_ROLL_Active := True;
               end if;

            end if;

         end if;

         --  Execute state VERTICAL
         VERTICAL_Update_Activated_Modes;

         if C2_VERTICAL_VS_SELECTED_Active then

            if VERTICAL_VS_Clear then

               --  Exit state SELECTED

               --  Close the inner composition of state SELECTED

               if C2_VERTICAL_VS_SELECTED_ACTIVE_Active then

                  --  Exit state ACTIVE
                  C2_VS_Active := False;
                  C2_VERTICAL_VS_SELECTED_ACTIVE_Active := False;
               end if;

               C2_VS_Selected := False;
               C2_VERTICAL_VS_SELECTED_Active := False;

               --  Enter state CLEARED
               C2_VERTICAL_VS_CLEARED_Active := True;
            else

               if C2_VERTICAL_VS_SELECTED_ACTIVE_Active then

                  if VERTICAL_New_Vertical_Mode_Activated then

                     --  Exit state ACTIVE
                     C2_VS_Active := False;

                     --  Exit state SELECTED
                     C2_VS_Selected := False;
                     C2_VERTICAL_VS_SELECTED_Active := False;
                     C2_VERTICAL_VS_SELECTED_ACTIVE_Active := False;

                     --  Enter state CLEARED
                     C2_VERTICAL_VS_CLEARED_Active := True;
                  end if;

               end if;

            end if;

         else

            if C2_VERTICAL_VS_CLEARED_Active then

               if VERTICAL_VS_Select then

                  --  Exit state CLEARED
                  C2_VERTICAL_VS_CLEARED_Active := False;

                  --  Enter state SELECTED
                  C2_VERTICAL_VS_SELECTED_Active := True;
                  C2_VS_Selected := True;

                  --  Enter state ACTIVE
                  C2_VERTICAL_VS_SELECTED_ACTIVE_Active := True;
                  C2_VS_Active := True;
               end if;

            end if;

         end if;

         if C2_VERTICAL_FLC_SELECTED_Active then

            if VERTICAL_FLC_Clear then

               --  Exit state SELECTED

               --  Close the inner composition of state SELECTED

               if C2_VERTICAL_FLC_SELECTED_ACTIVE_Active then

                  --  Exit state ACTIVE
                  C2_FLC_Active := False;
                  C2_VERTICAL_FLC_SELECTED_ACTIVE_Active := False;
               end if;

               C2_FLC_Selected := False;
               C2_VERTICAL_FLC_SELECTED_Active := False;

               --  Enter state CLEARED
               C2_VERTICAL_FLC_CLEARED_Active := True;
            else

               if C2_VERTICAL_FLC_SELECTED_ACTIVE_Active then

                  if VERTICAL_New_Vertical_Mode_Activated then

                     --  Exit state ACTIVE
                     C2_FLC_Active := False;

                     --  Exit state SELECTED
                     C2_FLC_Selected := False;
                     C2_VERTICAL_FLC_SELECTED_Active := False;
                     C2_VERTICAL_FLC_SELECTED_ACTIVE_Active := False;

                     --  Enter state CLEARED
                     C2_VERTICAL_FLC_CLEARED_Active := True;
                  end if;

               end if;

            end if;

         else

            if C2_VERTICAL_FLC_CLEARED_Active then

               if VERTICAL_FLC_Select then

                  --  Exit state CLEARED
                  C2_VERTICAL_FLC_CLEARED_Active := False;

                  --  Enter state SELECTED
                  C2_VERTICAL_FLC_SELECTED_Active := True;
                  C2_FLC_Selected := True;

                  --  Enter state ACTIVE
                  C2_VERTICAL_FLC_SELECTED_ACTIVE_Active := True;
                  C2_FLC_Active := True;
               end if;

            end if;

         end if;

         if C2_VERTICAL_ALT_SELECTED_Active then

            if VERTICAL_ALT_Clear then

               --  Exit state SELECTED

               --  Close the inner composition of state SELECTED

               if C2_VERTICAL_ALT_SELECTED_ACTIVE_Active then

                  --  Exit state ACTIVE
                  C2_ALT_Active := False;
                  C2_VERTICAL_ALT_SELECTED_ACTIVE_Active := False;
               end if;

               C2_ALT_Selected := False;
               C2_VERTICAL_ALT_SELECTED_Active := False;

               --  Enter state CLEARED
               C2_VERTICAL_ALT_CLEARED_Active := True;
            else

               if C2_VERTICAL_ALT_SELECTED_ACTIVE_Active then

                  if VERTICAL_New_Vertical_Mode_Activated then

                     --  Exit state ACTIVE
                     C2_ALT_Active := False;

                     --  Exit state SELECTED
                     C2_ALT_Selected := False;
                     C2_VERTICAL_ALT_SELECTED_Active := False;
                     C2_VERTICAL_ALT_SELECTED_ACTIVE_Active := False;

                     --  Enter state CLEARED
                     C2_VERTICAL_ALT_CLEARED_Active := True;
                  end if;

               end if;

            end if;

         else

            if C2_VERTICAL_ALT_CLEARED_Active then

               if VERTICAL_ALT_Select then

                  --  Exit state CLEARED
                  C2_VERTICAL_ALT_CLEARED_Active := False;

                  --  Enter state SELECTED
                  C2_VERTICAL_ALT_SELECTED_Active := True;
                  C2_ALT_Selected := True;

                  --  Enter state ACTIVE
                  C2_VERTICAL_ALT_SELECTED_ACTIVE_Active := True;
                  C2_ALT_Active := True;
               end if;

            end if;

         end if;

         if C2_VERTICAL_VAPPR_SELECTED_Active then

            if VERTICAL_VAPPR_Clear then

               --  Exit state SELECTED

               --  Close the inner composition of state SELECTED

               if C2_VERTICAL_VAPPR_SELECTED_ACTIVE_Active then

                  --  Exit state ACTIVE
                  C2_VAPPR_Active := False;
                  C2_VERTICAL_VAPPR_SELECTED_ACTIVE_Active := False;
               else

                  if C2_VERTICAL_VAPPR_SELECTED_ARMED_Active then

                     --  Exit state ARMED
                     C2_VERTICAL_VAPPR_SELECTED_ARMED_Active := False;
                  end if;

               end if;

               C2_VAPPR_Selected := False;
               C2_VERTICAL_VAPPR_SELECTED_Active := False;

               --  Enter state CLEARED
               C2_VERTICAL_VAPPR_CLEARED_Active := True;
            else

               if C2_VERTICAL_VAPPR_SELECTED_ACTIVE_Active then

                  if VERTICAL_New_Vertical_Mode_Activated then

                     --  Exit state ACTIVE
                     C2_VAPPR_Active := False;

                     --  Exit state SELECTED
                     C2_VAPPR_Selected := False;
                     C2_VERTICAL_VAPPR_SELECTED_Active := False;
                     C2_VERTICAL_VAPPR_SELECTED_ACTIVE_Active := False;

                     --  Enter state CLEARED
                     C2_VERTICAL_VAPPR_CLEARED_Active := True;
                  end if;

               else

                  if C2_VERTICAL_VAPPR_SELECTED_ARMED_Active then

                     if VERTICAL_VAPPR_Capture then

                        --  Exit state ARMED
                        C2_VERTICAL_VAPPR_SELECTED_ARMED_Active := False;

                        --  Enter state ACTIVE
                        C2_VERTICAL_VAPPR_SELECTED_ACTIVE_Active := True;
                        C2_VAPPR_Active := True;
                     end if;

                  end if;

               end if;

            end if;

         else

            if C2_VERTICAL_VAPPR_CLEARED_Active then

               if VERTICAL_VAPPR_Select then

                  --  Exit state CLEARED
                  C2_VERTICAL_VAPPR_CLEARED_Active := False;

                  --  Enter state SELECTED
                  C2_VERTICAL_VAPPR_SELECTED_Active := True;
                  C2_VAPPR_Selected := True;

                  --  Enter state ARMED
                  C2_VERTICAL_VAPPR_SELECTED_ARMED_Active := True;
               end if;

            end if;

         end if;

         if C2_VERTICAL_VGA_SELECTED_Active then

            if VERTICAL_VGA_Clear then

               --  Exit state SELECTED

               --  Close the inner composition of state SELECTED

               if C2_VERTICAL_VGA_SELECTED_ACTIVE_Active then

                  --  Exit state ACTIVE
                  C2_VGA_Active := False;
                  C2_VERTICAL_VGA_SELECTED_ACTIVE_Active := False;
               end if;

               C2_VGA_Selected := False;
               C2_VERTICAL_VGA_SELECTED_Active := False;

               --  Enter state CLEARED
               C2_VERTICAL_VGA_CLEARED_Active := True;
            else

               if C2_VERTICAL_VGA_SELECTED_ACTIVE_Active then

                  if VERTICAL_New_Vertical_Mode_Activated then

                     --  Exit state ACTIVE
                     C2_VGA_Active := False;

                     --  Exit state SELECTED
                     C2_VGA_Selected := False;
                     C2_VERTICAL_VGA_SELECTED_Active := False;
                     C2_VERTICAL_VGA_SELECTED_ACTIVE_Active := False;

                     --  Enter state CLEARED
                     C2_VERTICAL_VGA_CLEARED_Active := True;
                  end if;

               end if;

            end if;

         else

            if C2_VERTICAL_VGA_CLEARED_Active then

               if VERTICAL_VGA_Select then

                  --  Exit state CLEARED
                  C2_VERTICAL_VGA_CLEARED_Active := False;

                  --  Enter state SELECTED
                  C2_VERTICAL_VGA_SELECTED_Active := True;
                  C2_VGA_Selected := True;

                  --  Enter state ACTIVE
                  C2_VERTICAL_VGA_SELECTED_ACTIVE_Active := True;
                  C2_VGA_Active := True;
               end if;

            end if;

         end if;

         if C2_VERTICAL_ALTSEL_SELECTED_Active then

            if VERTICAL_ALTSEL_Clear then

               --  Exit state SELECTED

               --  Close the inner composition of state SELECTED

               if C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_Active then

                  --  Exit state ACTIVE

                  --  Close the inner composition of state ACTIVE

                  if C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_CAPTURE_Active then

                     --  Exit state CAPTURE
                     C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_CAPTURE_Active := False;
                  else

                     if C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_TRACK_Active then

                        --  Exit state TRACK
                        C2_ALTSEL_Track := False;
                        C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_TRACK_Active := False;
                     end if;

                  end if;

                  C2_ALTSEL_Active := False;
                  C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_Active := False;
               else

                  if C2_VERTICAL_ALTSEL_SELECTED_ARMED_Active then

                     --  Exit state ARMED
                     C2_VERTICAL_ALTSEL_SELECTED_ARMED_Active := False;
                  end if;

               end if;

               C2_ALTSEL_Selected := False;
               C2_VERTICAL_ALTSEL_SELECTED_Active := False;

               --  Enter state CLEARED
               C2_VERTICAL_ALTSEL_CLEARED_Active := True;
            else

               if C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_Active then

                  if VERTICAL_ALTSEL_Deactivate then

                     --  Exit state ACTIVE

                     --  Close the inner composition of state ACTIVE

                     if C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_CAPTURE_Active then

                        --  Exit state CAPTURE
                        C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_CAPTURE_Active := False;
                     else

                        if C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_TRACK_Active then

                           --  Exit state TRACK
                           C2_ALTSEL_Track := False;
                           C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_TRACK_Active := False;
                        end if;

                     end if;

                     C2_ALTSEL_Active := False;
                     C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_Active := False;

                     --  Enter state ARMED
                     C2_VERTICAL_ALTSEL_SELECTED_ARMED_Active := True;
                  else

                     if C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_CAPTURE_Active then

                        if VERTICAL_ALTSEL_Track then

                           --  Exit state CAPTURE
                           C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_CAPTURE_Active := False;

                           --  Enter state TRACK
                           C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_TRACK_Active := True;
                           C2_ALTSEL_Track := True;
                        end if;

                     end if;

                  end if;

               else

                  if C2_VERTICAL_ALTSEL_SELECTED_ARMED_Active then

                     if VERTICAL_ALTSEL_Capture then

                        --  Exit state ARMED
                        C2_VERTICAL_ALTSEL_SELECTED_ARMED_Active := False;

                        --  Enter state ACTIVE
                        C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_Active := True;
                        C2_ALTSEL_Active := True;

                        --  Enter state CAPTURE
                        C2_VERTICAL_ALTSEL_SELECTED_ACTIVE_CAPTURE_Active := True;
                     end if;

                  end if;

               end if;

            end if;

         else

            if C2_VERTICAL_ALTSEL_CLEARED_Active then

               if VERTICAL_ALTSEL_Select then

                  --  Exit state CLEARED
                  C2_VERTICAL_ALTSEL_CLEARED_Active := False;

                  --  Enter state SELECTED
                  C2_VERTICAL_ALTSEL_SELECTED_Active := True;
                  C2_ALTSEL_Selected := True;

                  --  Enter state ARMED
                  C2_VERTICAL_ALTSEL_SELECTED_ARMED_Active := True;
               end if;

            end if;

         end if;

         if C2_VERTICAL_PITCH_SELECTED_Active then

            if C2_VERTICAL_PITCH_SELECTED_ACTIVE_Active then

               if VERTICAL_Vertical_Mode_Active then

                  --  Exit state ACTIVE
                  C2_PITCH_Active := False;

                  --  Exit state SELECTED
                  C2_PITCH_Selected := False;
                  C2_VERTICAL_PITCH_SELECTED_Active := False;
                  C2_VERTICAL_PITCH_SELECTED_ACTIVE_Active := False;

                  --  Enter state CLEARED
                  C2_VERTICAL_PITCH_CLEARED_Active := True;
               end if;

            end if;

         else

            if C2_VERTICAL_PITCH_CLEARED_Active then

               if not  (VERTICAL_Vertical_Mode_Active) then

                  --  Exit state CLEARED
                  C2_VERTICAL_PITCH_CLEARED_Active := False;

                  --  Enter state SELECTED
                  C2_VERTICAL_PITCH_SELECTED_Active := True;
                  C2_PITCH_Selected := True;

                  --  Enter state ACTIVE
                  C2_VERTICAL_PITCH_SELECTED_ACTIVE_Active := True;
                  C2_PITCH_Active := True;
               end if;

            end if;

         end if;

      end if;

      --  Copy outputs Mode_Logic_Props/Mode_Logic/Flight_Modes
      Modes_On := C2_Modes_On;
      FD_On := C2_FD_On;
      Independent_Mode := C2_Independent_Mode;
      Active_Side := C2_Active_Side;
      ROLL_Selected := C2_ROLL_Selected;
      ROLL_Active := C2_ROLL_Active;
      HDG_Selected := C2_HDG_Selected;
      HDG_Active := C2_HDG_Active;
      NAV_Selected := C2_NAV_Selected;
      NAV_Active := C2_NAV_Active;
      LAPPR_Selected := C2_LAPPR_Selected;
      LAPPR_Active := C2_LAPPR_Active;
      LGA_Selected := C2_LGA_Selected;
      LGA_Active := C2_LGA_Active;
      PITCH_Selected := C2_PITCH_Selected;
      PITCH_Active := C2_PITCH_Active;
      VS_Selected := C2_VS_Selected;
      VS_Active := C2_VS_Active;
      FLC_Selected := C2_FLC_Selected;
      FLC_Active := C2_FLC_Active;
      ALT_Selected := C2_ALT_Selected;
      ALT_Active := C2_ALT_Active;
      ALTSEL_Selected := C2_ALTSEL_Selected;
      ALTSEL_Active := C2_ALTSEL_Active;
      ALTSEL_Track := C2_ALTSEL_Track;
      VAPPR_Selected := C2_VAPPR_Selected;
      VAPPR_Active := C2_VAPPR_Active;
      VGA_Selected := C2_VGA_Selected;
      VGA_Active := C2_VGA_Active;
   end comp;

   function FD_Turn_FD_On return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      aVarTruthTableCondition_4 : Boolean := False;
      aVarTruthTableCondition_5 : Boolean := False;
      aVarTruthTableCondition_6 : Boolean := False;
      aVarTruthTableCondition_7 : Boolean := False;
      aVarTruthTableCondition_8 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_FD_Switch_Pressed;
      aVarTruthTableCondition_2 := C2_When_AP_Engaged;
      aVarTruthTableCondition_3 := C2_Overspeed;
      aVarTruthTableCondition_4 := FD_Lateral_Mode_Manually_Selected;
      aVarTruthTableCondition_5 := FD_Vertical_Mode_Manually_Selected;
      aVarTruthTableCondition_6 := C2_Pilot_Flying_Transfer;
      aVarTruthTableCondition_7 := C2_Pilot_Flying_Side;
      aVarTruthTableCondition_8 := C2_Modes_On;

      if aVarTruthTableCondition_1 then
         r := True;
      else

         if aVarTruthTableCondition_2 then
            r := True;
         else

            if aVarTruthTableCondition_3 then
               r := True;
            else

               if aVarTruthTableCondition_4 then
                  r := True;
               else

                  if aVarTruthTableCondition_5 then
                     r := True;
                  else

                     if ((aVarTruthTableCondition_6)
                        and then (aVarTruthTableCondition_7))
                           and then (aVarTruthTableCondition_8)
                     then
                        r := True;
                     else
                        r := False;
                     end if;

                  end if;

               end if;

            end if;

         end if;

      end if;

      return r;
   end FD_Turn_FD_On;

   function FD_Turn_FD_Off return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_FD_Switch_Pressed;
      aVarTruthTableCondition_2 := C2_Overspeed;

      if (aVarTruthTableCondition_1)
         and then (not  (aVarTruthTableCondition_2))
      then
         r := True;
      else
         r := False;
      end if;

      return r;
   end FD_Turn_FD_Off;

   function FD_Lateral_Mode_Manually_Selected return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      aVarTruthTableCondition_4 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_HDG_Switch_Pressed;
      aVarTruthTableCondition_2 := C2_NAV_Switch_Pressed;
      aVarTruthTableCondition_3 := C2_APPR_Switch_Pressed;
      aVarTruthTableCondition_4 := C2_GA_Switch_Pressed;

      if aVarTruthTableCondition_1 then
         r := True;
      else

         if aVarTruthTableCondition_2 then
            r := True;
         else

            if aVarTruthTableCondition_3 then
               r := True;
            else

               if aVarTruthTableCondition_4 then
                  r := True;
               else
                  r := False;
               end if;

            end if;

         end if;

      end if;

      return r;
   end FD_Lateral_Mode_Manually_Selected;

   function FD_Vertical_Mode_Manually_Selected return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      aVarTruthTableCondition_4 : Boolean := False;
      aVarTruthTableCondition_5 : Boolean := False;
      aVarTruthTableCondition_6 : Boolean := False;
      aVarTruthTableCondition_7 : Boolean := False;
      aVarTruthTableCondition_8 : Boolean := False;
      aVarTruthTableCondition_9 : Boolean := False;
      aVarTruthTableCondition_10 : Boolean := False;
      aVarTruthTableCondition_11 : Boolean := False;
      aVarTruthTableCondition_12 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_Active_Side;
      aVarTruthTableCondition_2 := C2_VS_Switch_Pressed;
      aVarTruthTableCondition_3 := C2_FLC_Switch_Pressed;
      aVarTruthTableCondition_4 := C2_ALT_Switch_Pressed;
      aVarTruthTableCondition_5 := C2_APPR_Switch_Pressed;
      aVarTruthTableCondition_6 := C2_GA_Switch_Pressed;
      aVarTruthTableCondition_7 := C2_VS_Pitch_Wheel_Rotated;
      aVarTruthTableCondition_8 := C2_VS_Active;
      aVarTruthTableCondition_9 := C2_VAPPR_Active;
      aVarTruthTableCondition_10 := C2_Overspeed;
      aVarTruthTableCondition_11 := C2_ALTSEL_Target_Changed;
      aVarTruthTableCondition_12 := C2_ALTSEL_Active;

      if aVarTruthTableCondition_2 then
         r := True;
      else

         if aVarTruthTableCondition_3 then
            r := True;
         else

            if aVarTruthTableCondition_4 then
               r := True;
            else

               if aVarTruthTableCondition_5 then
                  r := True;
               else

                  if aVarTruthTableCondition_6 then
                     r := True;
                  else

                     if ((((aVarTruthTableCondition_1)
                        and then (aVarTruthTableCondition_7))
                           and then (not  (aVarTruthTableCondition_8)))
                              and then (not  (aVarTruthTableCondition_9)))
                                 and then (not  (aVarTruthTableCondition_10))
                     then
                        r := True;
                     else

                        if (aVarTruthTableCondition_11)
                           and then (aVarTruthTableCondition_12)
                        then
                           r := True;
                        else
                           r := False;
                        end if;

                     end if;

                  end if;

               end if;

            end if;

         end if;

      end if;

      return r;
   end FD_Vertical_Mode_Manually_Selected;

   function ANNUNCIATIONS_Turn_Annunciations_On return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_Is_AP_Engaged;
      aVarTruthTableCondition_2 := C2_Is_Offside_FD_On;
      aVarTruthTableCondition_3 := C2_FD_On;

      if aVarTruthTableCondition_1 then
         r := True;
      else

         if aVarTruthTableCondition_2 then
            r := True;
         else

            if aVarTruthTableCondition_3 then
               r := True;
            else
               r := False;
            end if;

         end if;

      end if;

      return r;
   end ANNUNCIATIONS_Turn_Annunciations_On;

   function ANNUNCIATIONS_Turn_Annunciations_Off return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_Is_AP_Engaged;
      aVarTruthTableCondition_2 := C2_Is_Offside_FD_On;
      aVarTruthTableCondition_3 := C2_FD_On;

      if ((not  (aVarTruthTableCondition_1))
         and then (not  (aVarTruthTableCondition_2)))
            and then (not  (aVarTruthTableCondition_3))
      then
         r := True;
      else
         r := False;
      end if;

      return r;
   end ANNUNCIATIONS_Turn_Annunciations_Off;

   function INDEPENDENT_In_Independent_Mode return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      aVarTruthTableCondition_4 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_VAPPR_Active;
      aVarTruthTableCondition_2 := C2_Is_Offside_VAPPR_Active;
      aVarTruthTableCondition_3 := C2_VGA_Active;
      aVarTruthTableCondition_4 := C2_Is_Offside_VGA_Active;

      if (aVarTruthTableCondition_1)
         and then (aVarTruthTableCondition_2)
      then
         r := True;
      else

         if (aVarTruthTableCondition_3)
            and then (aVarTruthTableCondition_4)
         then
            r := True;
         else
            r := False;
         end if;

      end if;

      return r;
   end INDEPENDENT_In_Independent_Mode;

   function ACTIVE_In_Active_Mode return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_Pilot_Flying_Side;
      aVarTruthTableCondition_2 := C2_Independent_Mode;

      if aVarTruthTableCondition_1 then
         r := True;
      else

         if aVarTruthTableCondition_2 then
            r := True;
         else
            r := False;
         end if;

      end if;

      return r;
   end ACTIVE_In_Active_Mode;

   function LATERAL_HDG_Select return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_HDG_Switch_Pressed;

      if aVarTruthTableCondition_1 then
         r := True;
      else
         r := False;
      end if;

      return r;
   end LATERAL_HDG_Select;

   function LATERAL_HDG_Clear return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_HDG_Switch_Pressed;
      aVarTruthTableCondition_2 := C2_Pilot_Flying_Transfer;
      aVarTruthTableCondition_3 := C2_Modes_On;

      if aVarTruthTableCondition_1 then
         r := True;
      else

         if aVarTruthTableCondition_2 then
            r := True;
         else

            if not  (aVarTruthTableCondition_3) then
               r := True;
            else
               r := False;
            end if;

         end if;

      end if;

      return r;
   end LATERAL_HDG_Clear;

   function LATERAL_HDG_Will_Be_Activated return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := True;
      aVarTruthTableCondition_2 := LATERAL_HDG_Select;

      if (aVarTruthTableCondition_1)
         and then (aVarTruthTableCondition_2)
      then
         r := True;
      else
         r := False;
      end if;

      return r;
   end LATERAL_HDG_Will_Be_Activated;

   function LATERAL_NAV_Select return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_NAV_Switch_Pressed;

      if aVarTruthTableCondition_1 then
         r := True;
      else
         r := False;
      end if;

      return r;
   end LATERAL_NAV_Select;

   function LATERAL_NAV_Capture return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_NAV_Capture_Condition_Met;

      if aVarTruthTableCondition_1 then
         r := True;
      else
         r := False;
      end if;

      return r;
   end LATERAL_NAV_Capture;

   function LATERAL_NAV_Clear return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      aVarTruthTableCondition_4 : Boolean := False;
      aVarTruthTableCondition_5 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_NAV_Switch_Pressed;
      aVarTruthTableCondition_2 := C2_Selected_NAV_Source_Changed;
      aVarTruthTableCondition_3 := C2_Selected_NAV_Frequency_Changed;
      aVarTruthTableCondition_4 := C2_Pilot_Flying_Transfer;
      aVarTruthTableCondition_5 := C2_Modes_On;

      if aVarTruthTableCondition_1 then
         r := True;
      else

         if aVarTruthTableCondition_2 then
            r := True;
         else

            if aVarTruthTableCondition_3 then
               r := True;
            else

               if aVarTruthTableCondition_4 then
                  r := True;
               else

                  if not  (aVarTruthTableCondition_5) then
                     r := True;
                  else
                     r := False;
                  end if;

               end if;

            end if;

         end if;

      end if;

      return r;
   end LATERAL_NAV_Clear;

   function LATERAL_NAV_Will_Be_Activated return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := True;
      aVarTruthTableCondition_2 := LATERAL_NAV_Capture;
      aVarTruthTableCondition_3 := LATERAL_NAV_Clear;

      if ((aVarTruthTableCondition_1)
         and then (aVarTruthTableCondition_2))
            and then (not  (aVarTruthTableCondition_3))
      then
         r := True;
      else
         r := False;
      end if;

      return r;
   end LATERAL_NAV_Will_Be_Activated;

   function LATERAL_LAPPR_Select return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_APPR_Switch_Pressed;

      if aVarTruthTableCondition_1 then
         r := True;
      else
         r := False;
      end if;

      return r;
   end LATERAL_LAPPR_Select;

   function LATERAL_LAPPR_Capture return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_LAPPR_Capture_Condition_Met;

      if aVarTruthTableCondition_1 then
         r := True;
      else
         r := False;
      end if;

      return r;
   end LATERAL_LAPPR_Capture;

   function LATERAL_LAPPR_Clear return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      aVarTruthTableCondition_4 : Boolean := False;
      aVarTruthTableCondition_5 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_APPR_Switch_Pressed;
      aVarTruthTableCondition_2 := C2_Selected_NAV_Source_Changed;
      aVarTruthTableCondition_3 := C2_Selected_NAV_Frequency_Changed;
      aVarTruthTableCondition_4 := C2_Pilot_Flying_Transfer;
      aVarTruthTableCondition_5 := C2_Modes_On;

      if aVarTruthTableCondition_1 then
         r := True;
      else

         if aVarTruthTableCondition_2 then
            r := True;
         else

            if aVarTruthTableCondition_3 then
               r := True;
            else

               if aVarTruthTableCondition_4 then
                  r := True;
               else

                  if not  (aVarTruthTableCondition_5) then
                     r := True;
                  else
                     r := False;
                  end if;

               end if;

            end if;

         end if;

      end if;

      return r;
   end LATERAL_LAPPR_Clear;

   function LATERAL_LAPPR_Will_Be_Activated return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := True;
      aVarTruthTableCondition_2 := LATERAL_LAPPR_Capture;
      aVarTruthTableCondition_3 := LATERAL_LAPPR_Clear;

      if ((aVarTruthTableCondition_1)
         and then (aVarTruthTableCondition_2))
            and then (not  (aVarTruthTableCondition_3))
      then
         r := True;
      else
         r := False;
      end if;

      return r;
   end LATERAL_LAPPR_Will_Be_Activated;

   function LATERAL_LGA_Select return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_GA_Switch_Pressed;
      aVarTruthTableCondition_2 := C2_Overspeed;

      if (aVarTruthTableCondition_1)
         and then (not  (aVarTruthTableCondition_2))
      then
         r := True;
      else
         r := False;
      end if;

      return r;
   end LATERAL_LGA_Select;

   function LATERAL_LGA_Clear return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      aVarTruthTableCondition_4 : Boolean := False;
      aVarTruthTableCondition_5 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_When_AP_Engaged;
      aVarTruthTableCondition_2 := C2_VGA_Active;
      aVarTruthTableCondition_3 := C2_SYNC_Switch_Pressed;
      aVarTruthTableCondition_4 := C2_Pilot_Flying_Transfer;
      aVarTruthTableCondition_5 := C2_Modes_On;

      if aVarTruthTableCondition_1 then
         r := True;
      else

         if not  (aVarTruthTableCondition_2) then
            r := True;
         else

            if aVarTruthTableCondition_3 then
               r := True;
            else

               if aVarTruthTableCondition_4 then
                  r := True;
               else

                  if not  (aVarTruthTableCondition_5) then
                     r := True;
                  else
                     r := False;
                  end if;

               end if;

            end if;

         end if;

      end if;

      return r;
   end LATERAL_LGA_Clear;

   function LATERAL_LGA_Will_Be_Activated return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := True;
      aVarTruthTableCondition_2 := LATERAL_LGA_Select;

      if (aVarTruthTableCondition_1)
         and then (aVarTruthTableCondition_2)
      then
         r := True;
      else
         r := False;
      end if;

      return r;
   end LATERAL_LGA_Will_Be_Activated;

   procedure LATERAL_Update_Activated_Modes is
   begin
      C2_LATERAL_HDG_Will_Be_Activated := LATERAL_HDG_Will_Be_Activated;
      C2_LATERAL_NAV_Will_Be_Activated := LATERAL_NAV_Will_Be_Activated;
      C2_LATERAL_LAPPR_Will_Be_Activated := LATERAL_LAPPR_Will_Be_Activated;
      C2_LATERAL_LGA_Will_Be_Activated := LATERAL_LGA_Will_Be_Activated;
   end LATERAL_Update_Activated_Modes;

   function LATERAL_Lateral_Mode_Active return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      aVarTruthTableCondition_4 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_HDG_Active;
      aVarTruthTableCondition_2 := C2_NAV_Active;
      aVarTruthTableCondition_3 := C2_LAPPR_Active;
      aVarTruthTableCondition_4 := C2_LGA_Active;

      if aVarTruthTableCondition_1 then
         r := True;
      else

         if aVarTruthTableCondition_2 then
            r := True;
         else

            if aVarTruthTableCondition_3 then
               r := True;
            else

               if aVarTruthTableCondition_4 then
                  r := True;
               else
                  r := False;
               end if;

            end if;

         end if;

      end if;

      return r;
   end LATERAL_Lateral_Mode_Active;

   function LATERAL_New_Lateral_Mode_Activated return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      aVarTruthTableCondition_4 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_LATERAL_HDG_Will_Be_Activated;
      aVarTruthTableCondition_2 := C2_LATERAL_NAV_Will_Be_Activated;
      aVarTruthTableCondition_3 := C2_LATERAL_LAPPR_Will_Be_Activated;
      aVarTruthTableCondition_4 := C2_LATERAL_LGA_Will_Be_Activated;

      if aVarTruthTableCondition_1 then
         r := True;
      else

         if aVarTruthTableCondition_2 then
            r := True;
         else

            if aVarTruthTableCondition_3 then
               r := True;
            else

               if aVarTruthTableCondition_4 then
                  r := True;
               else
                  r := False;
               end if;

            end if;

         end if;

      end if;

      return r;
   end LATERAL_New_Lateral_Mode_Activated;

   function VERTICAL_VS_Select return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_VS_Switch_Pressed;
      aVarTruthTableCondition_2 := C2_Overspeed;
      aVarTruthTableCondition_3 := C2_VAPPR_Active;

      if ((aVarTruthTableCondition_1)
         and then (not  (aVarTruthTableCondition_2)))
            and then (not  (aVarTruthTableCondition_3))
      then
         r := True;
      else
         r := False;
      end if;

      return r;
   end VERTICAL_VS_Select;

   function VERTICAL_VS_Clear return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_VS_Switch_Pressed;
      aVarTruthTableCondition_2 := C2_Pilot_Flying_Transfer;
      aVarTruthTableCondition_3 := C2_Modes_On;

      if aVarTruthTableCondition_1 then
         r := True;
      else

         if aVarTruthTableCondition_2 then
            r := True;
         else

            if not  (aVarTruthTableCondition_3) then
               r := True;
            else
               r := False;
            end if;

         end if;

      end if;

      return r;
   end VERTICAL_VS_Clear;

   function VERTICAL_VS_Will_Be_Activated return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := True;
      aVarTruthTableCondition_2 := VERTICAL_VS_Select;

      if (aVarTruthTableCondition_1)
         and then (aVarTruthTableCondition_2)
      then
         r := True;
      else
         r := False;
      end if;

      return r;
   end VERTICAL_VS_Will_Be_Activated;

   function VERTICAL_FLC_Select return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      aVarTruthTableCondition_4 : Boolean := False;
      aVarTruthTableCondition_5 : Boolean := False;
      aVarTruthTableCondition_6 : Boolean := False;
      aVarTruthTableCondition_7 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_FLC_Switch_Pressed;
      aVarTruthTableCondition_2 := C2_VAPPR_Active;
      aVarTruthTableCondition_3 := C2_Overspeed;
      aVarTruthTableCondition_4 := C2_ALT_Active;
      aVarTruthTableCondition_5 := C2_VERTICAL_ALT_Will_Be_Activated;
      aVarTruthTableCondition_6 := C2_ALTSEL_Active;
      aVarTruthTableCondition_7 := C2_VERTICAL_ALTSEL_Will_Be_Activated;

      if (aVarTruthTableCondition_1)
         and then (not  (aVarTruthTableCondition_2))
      then
         r := True;
      else

         if ((((aVarTruthTableCondition_3)
            and then (not  (aVarTruthTableCondition_4)))
               and then (not  (aVarTruthTableCondition_5)))
                  and then (not  (aVarTruthTableCondition_6)))
                     and then (not  (aVarTruthTableCondition_7))
         then
            r := True;
         else
            r := False;
         end if;

      end if;

      return r;
   end VERTICAL_FLC_Select;

   function VERTICAL_FLC_Clear return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      aVarTruthTableCondition_4 : Boolean := False;
      aVarTruthTableCondition_5 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_FLC_Switch_Pressed;
      aVarTruthTableCondition_2 := C2_Overspeed;
      aVarTruthTableCondition_3 := C2_VS_Pitch_Wheel_Rotated;
      aVarTruthTableCondition_4 := C2_Pilot_Flying_Transfer;
      aVarTruthTableCondition_5 := C2_Modes_On;

      if (aVarTruthTableCondition_1)
         and then (not  (aVarTruthTableCondition_2))
      then
         r := True;
      else

         if (not  (aVarTruthTableCondition_2))
            and then (aVarTruthTableCondition_3)
         then
            r := True;
         else

            if aVarTruthTableCondition_4 then
               r := True;
            else

               if not  (aVarTruthTableCondition_5) then
                  r := True;
               else
                  r := False;
               end if;

            end if;

         end if;

      end if;

      return r;
   end VERTICAL_FLC_Clear;

   function VERTICAL_FLC_Will_Be_Activated return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := True;
      aVarTruthTableCondition_2 := VERTICAL_FLC_Select;

      if (aVarTruthTableCondition_1)
         and then (aVarTruthTableCondition_2)
      then
         r := True;
      else
         r := False;
      end if;

      return r;
   end VERTICAL_FLC_Will_Be_Activated;

   function VERTICAL_ALT_Select return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      aVarTruthTableCondition_4 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_ALT_Switch_Pressed;
      aVarTruthTableCondition_2 := C2_VAPPR_Active;
      aVarTruthTableCondition_3 := C2_ALTSEL_Target_Changed;
      aVarTruthTableCondition_4 := C2_ALTSEL_Track;

      if (aVarTruthTableCondition_1)
         and then (not  (aVarTruthTableCondition_2))
      then
         r := True;
      else

         if (aVarTruthTableCondition_3)
            and then (aVarTruthTableCondition_4)
         then
            r := True;
         else
            r := False;
         end if;

      end if;

      return r;
   end VERTICAL_ALT_Select;

   function VERTICAL_ALT_Clear return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      aVarTruthTableCondition_4 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_ALT_Switch_Pressed;
      aVarTruthTableCondition_2 := C2_VS_Pitch_Wheel_Rotated;
      aVarTruthTableCondition_3 := C2_Pilot_Flying_Transfer;
      aVarTruthTableCondition_4 := C2_Modes_On;

      if aVarTruthTableCondition_1 then
         r := True;
      else

         if aVarTruthTableCondition_2 then
            r := True;
         else

            if aVarTruthTableCondition_3 then
               r := True;
            else

               if not  (aVarTruthTableCondition_4) then
                  r := True;
               else
                  r := False;
               end if;

            end if;

         end if;

      end if;

      return r;
   end VERTICAL_ALT_Clear;

   function VERTICAL_ALT_Will_Be_Activated return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := True;
      aVarTruthTableCondition_2 := VERTICAL_ALT_Select;

      if (aVarTruthTableCondition_1)
         and then (aVarTruthTableCondition_2)
      then
         r := True;
      else
         r := False;
      end if;

      return r;
   end VERTICAL_ALT_Will_Be_Activated;

   function VERTICAL_VAPPR_Select return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_APPR_Switch_Pressed;

      if aVarTruthTableCondition_1 then
         r := True;
      else
         r := False;
      end if;

      return r;
   end VERTICAL_VAPPR_Select;

   function VERTICAL_VAPPR_Capture return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_VAPPR_Capture_Condition_Met;
      aVarTruthTableCondition_2 := C2_LAPPR_Active;
      aVarTruthTableCondition_3 := C2_Overspeed;

      if ((aVarTruthTableCondition_1)
         and then (aVarTruthTableCondition_2))
            and then (not  (aVarTruthTableCondition_3))
      then
         r := True;
      else
         r := False;
      end if;

      return r;
   end VERTICAL_VAPPR_Capture;

   function VERTICAL_VAPPR_Clear return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      aVarTruthTableCondition_4 : Boolean := False;
      aVarTruthTableCondition_5 : Boolean := False;
      aVarTruthTableCondition_6 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_APPR_Switch_Pressed;
      aVarTruthTableCondition_2 := C2_LAPPR_Selected;
      aVarTruthTableCondition_3 := C2_Selected_NAV_Source_Changed;
      aVarTruthTableCondition_4 := C2_Selected_NAV_Frequency_Changed;
      aVarTruthTableCondition_5 := C2_Pilot_Flying_Transfer;
      aVarTruthTableCondition_6 := C2_Modes_On;

      if aVarTruthTableCondition_1 then
         r := True;
      else

         if not  (aVarTruthTableCondition_2) then
            r := True;
         else

            if aVarTruthTableCondition_3 then
               r := True;
            else

               if aVarTruthTableCondition_4 then
                  r := True;
               else

                  if aVarTruthTableCondition_5 then
                     r := True;
                  else

                     if not  (aVarTruthTableCondition_6) then
                        r := True;
                     else
                        r := False;
                     end if;

                  end if;

               end if;

            end if;

         end if;

      end if;

      return r;
   end VERTICAL_VAPPR_Clear;

   function VERTICAL_VAPPR_Will_Be_Activated return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := True;
      aVarTruthTableCondition_2 := VERTICAL_VAPPR_Capture;
      aVarTruthTableCondition_3 := VERTICAL_VAPPR_Clear;

      if ((aVarTruthTableCondition_1)
         and then (aVarTruthTableCondition_2))
            and then (not  (aVarTruthTableCondition_3))
      then
         r := True;
      else
         r := False;
      end if;

      return r;
   end VERTICAL_VAPPR_Will_Be_Activated;

   function VERTICAL_VGA_Select return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_GA_Switch_Pressed;
      aVarTruthTableCondition_2 := C2_Overspeed;

      if (aVarTruthTableCondition_1)
         and then (not  (aVarTruthTableCondition_2))
      then
         r := True;
      else
         r := False;
      end if;

      return r;
   end VERTICAL_VGA_Select;

   function VERTICAL_VGA_Clear return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      aVarTruthTableCondition_4 : Boolean := False;
      aVarTruthTableCondition_5 : Boolean := False;
      aVarTruthTableCondition_6 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_When_AP_Engaged;
      aVarTruthTableCondition_2 := C2_LGA_Active;
      aVarTruthTableCondition_3 := C2_SYNC_Switch_Pressed;
      aVarTruthTableCondition_4 := C2_VS_Pitch_Wheel_Rotated;
      aVarTruthTableCondition_5 := C2_Pilot_Flying_Transfer;
      aVarTruthTableCondition_6 := C2_Modes_On;

      if aVarTruthTableCondition_1 then
         r := True;
      else

         if not  (aVarTruthTableCondition_2) then
            r := True;
         else

            if aVarTruthTableCondition_3 then
               r := True;
            else

               if aVarTruthTableCondition_4 then
                  r := True;
               else

                  if aVarTruthTableCondition_5 then
                     r := True;
                  else

                     if not  (aVarTruthTableCondition_6) then
                        r := True;
                     else
                        r := False;
                     end if;

                  end if;

               end if;

            end if;

         end if;

      end if;

      return r;
   end VERTICAL_VGA_Clear;

   function VERTICAL_VGA_Will_Be_Activated return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := True;
      aVarTruthTableCondition_2 := VERTICAL_VGA_Select;

      if (aVarTruthTableCondition_1)
         and then (aVarTruthTableCondition_2)
      then
         r := True;
      else
         r := False;
      end if;

      return r;
   end VERTICAL_VGA_Will_Be_Activated;

   function VERTICAL_ALTSEL_Select return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_VAPPR_Active;
      aVarTruthTableCondition_2 := C2_VGA_Active;
      aVarTruthTableCondition_3 := C2_ALT_Active;

      if ((not  (aVarTruthTableCondition_1))
         and then (not  (aVarTruthTableCondition_2)))
            and then (not  (aVarTruthTableCondition_3))
      then
         r := True;
      else
         r := False;
      end if;

      return r;
   end VERTICAL_ALTSEL_Select;

   function VERTICAL_ALTSEL_Capture return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_ALTSEL_Capture_Condition_Met;

      if aVarTruthTableCondition_1 then
         r := True;
      else
         r := False;
      end if;

      return r;
   end VERTICAL_ALTSEL_Capture;

   function VERTICAL_ALTSEL_Track return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_ALTSEL_Track_Condition_Met;

      if aVarTruthTableCondition_1 then
         r := True;
      else
         r := False;
      end if;

      return r;
   end VERTICAL_ALTSEL_Track;

   function VERTICAL_ALTSEL_Deactivate return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      aVarTruthTableCondition_4 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_ALTSEL_Target_Changed;
      aVarTruthTableCondition_2 := C2_VS_Pitch_Wheel_Rotated;
      aVarTruthTableCondition_3 := C2_Pilot_Flying_Transfer;
      aVarTruthTableCondition_4 := VERTICAL_New_Vertical_Mode_Activated;

      if aVarTruthTableCondition_1 then
         r := True;
      else

         if aVarTruthTableCondition_2 then
            r := True;
         else

            if aVarTruthTableCondition_3 then
               r := True;
            else

               if aVarTruthTableCondition_4 then
                  r := True;
               else
                  r := False;
               end if;

            end if;

         end if;

      end if;

      return r;
   end VERTICAL_ALTSEL_Deactivate;

   function VERTICAL_ALTSEL_Clear return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      aVarTruthTableCondition_4 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_VAPPR_Active;
      aVarTruthTableCondition_2 := C2_VGA_Active;
      aVarTruthTableCondition_3 := C2_ALT_Active;
      aVarTruthTableCondition_4 := C2_Modes_On;

      if aVarTruthTableCondition_1 then
         r := True;
      else

         if aVarTruthTableCondition_2 then
            r := True;
         else

            if aVarTruthTableCondition_3 then
               r := True;
            else

               if not  (aVarTruthTableCondition_4) then
                  r := True;
               else
                  r := False;
               end if;

            end if;

         end if;

      end if;

      return r;
   end VERTICAL_ALTSEL_Clear;

   function VERTICAL_ALTSEL_Will_Be_Activated return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := True;
      aVarTruthTableCondition_2 := VERTICAL_ALTSEL_Capture;
      aVarTruthTableCondition_3 := VERTICAL_ALTSEL_Clear;

      if ((aVarTruthTableCondition_1)
         and then (aVarTruthTableCondition_2))
            and then (not  (aVarTruthTableCondition_3))
      then
         r := True;
      else
         r := False;
      end if;

      return r;
   end VERTICAL_ALTSEL_Will_Be_Activated;

   procedure VERTICAL_Update_Activated_Modes is
   begin
      C2_VERTICAL_VS_Will_Be_Activated := VERTICAL_VS_Will_Be_Activated;
      C2_VERTICAL_FLC_Will_Be_Activated := VERTICAL_FLC_Will_Be_Activated;
      C2_VERTICAL_ALT_Will_Be_Activated := VERTICAL_ALT_Will_Be_Activated;
      C2_VERTICAL_ALTSEL_Will_Be_Activated := VERTICAL_ALTSEL_Will_Be_Activated;
      C2_VERTICAL_VAPPR_Will_Be_Activated := VERTICAL_VAPPR_Will_Be_Activated;
      C2_VERTICAL_VGA_Will_Be_Activated := VERTICAL_VGA_Will_Be_Activated;
   end VERTICAL_Update_Activated_Modes;

   function VERTICAL_New_Vertical_Mode_Activated return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      aVarTruthTableCondition_4 : Boolean := False;
      aVarTruthTableCondition_5 : Boolean := False;
      aVarTruthTableCondition_6 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_VERTICAL_VS_Will_Be_Activated;
      aVarTruthTableCondition_2 := C2_VERTICAL_FLC_Will_Be_Activated;
      aVarTruthTableCondition_3 := C2_VERTICAL_ALT_Will_Be_Activated;
      aVarTruthTableCondition_4 := C2_VERTICAL_ALTSEL_Will_Be_Activated;
      aVarTruthTableCondition_5 := C2_VERTICAL_VAPPR_Will_Be_Activated;
      aVarTruthTableCondition_6 := C2_VERTICAL_VGA_Will_Be_Activated;

      if aVarTruthTableCondition_1 then
         r := True;
      else

         if aVarTruthTableCondition_2 then
            r := True;
         else

            if aVarTruthTableCondition_3 then
               r := True;
            else

               if aVarTruthTableCondition_4 then
                  r := True;
               else

                  if aVarTruthTableCondition_5 then
                     r := True;
                  else

                     if aVarTruthTableCondition_6 then
                        r := True;
                     else
                        r := False;
                     end if;

                  end if;

               end if;

            end if;

         end if;

      end if;

      return r;
   end VERTICAL_New_Vertical_Mode_Activated;

   function VERTICAL_Vertical_Mode_Active return Boolean is
      use type Boolean;
      aVarTruthTableCondition_1 : Boolean := False;
      aVarTruthTableCondition_2 : Boolean := False;
      aVarTruthTableCondition_3 : Boolean := False;
      aVarTruthTableCondition_4 : Boolean := False;
      aVarTruthTableCondition_5 : Boolean := False;
      aVarTruthTableCondition_6 : Boolean := False;
      r : Boolean := False;
   begin
      aVarTruthTableCondition_1 := C2_VS_Active;
      aVarTruthTableCondition_2 := C2_FLC_Active;
      aVarTruthTableCondition_3 := C2_ALT_Active;
      aVarTruthTableCondition_4 := C2_ALTSEL_Active;
      aVarTruthTableCondition_5 := C2_VAPPR_Active;
      aVarTruthTableCondition_6 := C2_VGA_Active;

      if aVarTruthTableCondition_1 then
         r := True;
      else

         if aVarTruthTableCondition_2 then
            r := True;
         else

            if aVarTruthTableCondition_3 then
               r := True;
            else

               if aVarTruthTableCondition_4 then
                  r := True;
               else

                  if aVarTruthTableCondition_5 then
                     r := True;
                  else

                     if aVarTruthTableCondition_6 then
                        r := True;
                     else
                        r := False;
                     end if;

                  end if;

               end if;

            end if;

         end if;

      end if;

      return r;
   end VERTICAL_Vertical_Mode_Active;
end Flight_Modes;
--  @EOF
