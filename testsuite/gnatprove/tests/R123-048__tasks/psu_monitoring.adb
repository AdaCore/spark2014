pragma Profile (Ravenscar);
pragma SPARK_Mode;

with Ada.Text_IO; use Ada.Text_IO;

with PSU_Control; use PSU_Control;
with PSU_Simulation; use PSU_Simulation;

package body PSU_Monitoring is

   protected body Monitoring_Interface_T is

      function is_all_config_set return Boolean is
      begin
         return monitor_pfc_voltage_config_set and monitor_pfc_current_config_set and monitor_output_voltage_config_set and monitor_output_current_config_set;
      end is_all_config_set;

      procedure set_monitor_pfc_voltage_config (new_monitor_config : in Monitor_Config_T) is
      begin
         monitor_pfc_voltage_config := new_monitor_config;
         monitor_pfc_voltage_config_set := True;
      end set_monitor_pfc_voltage_config;

      function get_monitor_pfc_voltage_config return Monitor_Config_T is
      begin
         return monitor_pfc_voltage_config;
      end get_monitor_pfc_voltage_config;

      procedure set_monitor_pfc_current_config (new_monitor_config : in Monitor_Config_T) is
      begin
         monitor_pfc_current_config := new_monitor_config;
         monitor_pfc_current_config_set := True;
      end set_monitor_pfc_current_config;

      function get_monitor_pfc_current_config return Monitor_Config_T is
      begin
         return monitor_pfc_current_config;
      end get_monitor_pfc_current_config;

      procedure set_monitor_output_voltage_config (new_monitor_config : in Monitor_Config_T) is
      begin
         monitor_output_voltage_config := new_monitor_config;
         monitor_output_voltage_config_set := True;
      end set_monitor_output_voltage_config;

      function get_monitor_output_voltage_config return Monitor_Config_T is
      begin
         return monitor_output_voltage_config;
      end get_monitor_output_voltage_config;

      procedure set_monitor_output_current_config (new_monitor_config : in Monitor_Config_T) is
      begin
         monitor_output_current_config := new_monitor_config;
         monitor_output_current_config_set := True;
      end set_monitor_output_current_config;

      function get_monitor_output_current_config return Monitor_Config_T is
      begin
         return monitor_output_current_config;
      end get_monitor_output_current_config;

   end Monitoring_Interface_T;

   function is_within_limits (monitor : in Monitor_T; signal_value : in Float) return Boolean is
      within_limits : Boolean := False;
   begin
      case monitor.config.monitoring_mode is
         when mean_based =>
            if abs (monitor.config.mean - signal_value) <= monitor.config.maximum_deviation then
               within_limits := True;
            end if;

         when threshold_based =>
            if signal_value >= monitor.config.lower_threshold or signal_value <= monitor.config.upper_threshold then
               within_limits := True;
            end if;
      end case;

      return within_limits;

   end is_within_limits;

   function is_within_expanded_limits (monitor : in Monitor_T; signal_value : in Float) return Boolean is
      within_expanded_limits : Boolean := False;

      expanded_lower_threshold : Float_Signed1000;
      expanded_upper_threshold : Float_Signed1000;
   begin
      case monitor.config.monitoring_mode is
         when mean_based =>
            if abs (monitor.config.mean - signal_value) <= (monitor.config.maximum_deviation * monitor.config.settling_tolerance_expansion) then
               within_expanded_limits := True;
            end if;

         when threshold_based =>
            --  Calculate expanded thresholds
            if monitor.config.lower_threshold >= 0.0 then
               expanded_lower_threshold := monitor.config.lower_threshold / monitor.config.settling_tolerance_expansion;
            else
               expanded_lower_threshold := monitor.config.lower_threshold * monitor.config.settling_tolerance_expansion;
            end if;

            if monitor.config.upper_threshold >= 0.0 then
               expanded_upper_threshold := monitor.config.upper_threshold * monitor.config.settling_tolerance_expansion;
            else
               expanded_upper_threshold := monitor.config.upper_threshold / monitor.config.settling_tolerance_expansion;
            end if;

            --  Check limits with expanded thresholds
            if signal_value >= expanded_lower_threshold or signal_value <= expanded_upper_threshold then
               within_expanded_limits := True;
            end if;
      end case;

      return within_expanded_limits;

   end is_within_expanded_limits;

   procedure monitor_signal (monitor : in out Monitor_T; signal_value : in Float) is
      all_config_is_set : constant Boolean := monitoring_interface.is_all_config_set;
   begin
      pragma Assert (all_config_is_set);
      monitor.current_state := monitor.next_state;

      case monitor.current_state is
         when reset =>
            --  Deactivate controllers
            Ctrl.Set_Safety_State (False);
            monitor.next_state := startup;
            monitor.timer := Milliseconds (0);
         when startup =>
            --  Activate controllers
            Ctrl.Set_Safety_State (True);

            if is_within_limits (monitor, signal_value) then
               monitor.next_state := settling;
               monitor.timer := Milliseconds (0);
            elsif monitor.timer >= monitor.config.startup_time then
               monitor.next_state := shutdown;
               monitor.timer := Milliseconds (0);
            else
               monitor.next_state := startup;
               monitor.timer := monitor.timer + TASK_PERIOD;
            end if;

         when settling =>
            if is_within_expanded_limits (monitor, signal_value) = False then
               monitor.next_state := shutdown;
               monitor.timer := Milliseconds (0);
            elsif monitor.timer >= monitor.config.settling_time then
               monitor.next_state := active;
            else
               monitor.next_state := settling;
               monitor.timer := monitor.timer + TASK_PERIOD;
            end if;

         when active =>
            if is_within_limits (monitor, signal_value) = False then
               monitor.next_state := alert;
               monitor.timer := Milliseconds (0);
            else
               monitor.next_state := active;
            end if;

         when alert =>
            if is_within_limits (monitor, signal_value) then
               monitor.next_state := settling;
               monitor.timer := Milliseconds (0);
            elsif monitor.timer >= monitor.config.violation_time then
               monitor.next_state := shutdown;
               monitor.timer := Milliseconds (0);
            else
               monitor.next_state := alert;
               monitor.timer := monitor.timer + TASK_PERIOD;
            end if;

         when shutdown =>
            --  Deactivate controllers
            Ctrl.Set_Safety_State (False);

            if monitor.timer >= monitor.config.retry_time then
               monitor.next_state := startup;
               monitor.timer := Milliseconds (0);
            else
               monitor.next_state := shutdown;
               monitor.timer := monitor.timer + TASK_PERIOD;
            end if;
      end case;
   end monitor_signal;

   procedure do_monitoring is
      U_C1 : constant Float := Sim.Get_U_C1;
      I_L1 : constant Float := Sim.Get_I_L1;
      U_C2 : constant Float := Sim.Get_U_C2;
      I_L2 : constant Float := Sim.Get_I_L2;
   begin
      pragma Assert (U_C1 in Float_Signed1000);
      pragma Assert (I_L1 in Float_Signed1000);
      pragma Assert (U_C2 in Float_Signed1000);
      pragma Assert (I_L2 in Float_Signed1000);

      --  Monitor PFC intermediate voltage
      monitor_signal (monitor_pfc_voltage, U_C1);
      --  Monitor PFC inductor current
      monitor_signal (monitor_pfc_current, I_L1);
      --  Monitor output voltage
      monitor_signal (monitor_output_voltage, U_C2);
      --  Monitor output inductor current
      monitor_signal (monitor_output_current, I_L2);
   end do_monitoring;

   task body monitoring_task is
      next_time : Time := Clock;
   begin
      --  Superloop
      loop
         Put_Line ("Run task monitoring");
         --  Load monitor configuration
         monitor_pfc_voltage.config := monitoring_interface.get_monitor_pfc_voltage_config;
         monitor_pfc_current.config := monitoring_interface.get_monitor_pfc_current_config;
         monitor_output_voltage.config := monitoring_interface.get_monitor_output_voltage_config;
         monitor_output_current.config := monitoring_interface.get_monitor_output_current_config;

         declare
            --  See https://goo.gl/NBXa7y
            all_config_is_set : constant Boolean := monitoring_interface.is_all_config_set;
         begin
            --  Check if module has been configured correctly
            --  Don't do anything otherwise
            if all_config_is_set then
               do_monitoring;
            end if;
         end;

         next_time := next_time + TASK_PERIOD;
         delay until next_time;
      end loop;
   end monitoring_task;

end PSU_Monitoring;
