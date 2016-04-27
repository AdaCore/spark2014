pragma Ada_95;
pragma Source_File_Name (ada_main, Spec_File_Name => "b~spark_dns_main.ads");
pragma Source_File_Name (ada_main, Body_File_Name => "b~spark_dns_main.adb");

with System.Restrictions;
with Ada.Exceptions;

package body ada_main is
   pragma Warnings (Off);

   E147 : Short_Integer; pragma Import (Ada, E147, "system__os_lib_E");
   E020 : Short_Integer; pragma Import (Ada, E020, "system__soft_links_E");
   E255 : Short_Integer; pragma Import (Ada, E255, "system__fat_flt_E");
   E231 : Short_Integer; pragma Import (Ada, E231, "system__fat_llf_E");
   E014 : Short_Integer; pragma Import (Ada, E014, "system__exception_table_E");
   E126 : Short_Integer; pragma Import (Ada, E126, "ada__io_exceptions_E");
   E011 : Short_Integer; pragma Import (Ada, E011, "ada__strings_E");
   E053 : Short_Integer; pragma Import (Ada, E053, "ada__strings__maps_E");
   E057 : Short_Integer; pragma Import (Ada, E057, "ada__strings__maps__constants_E");
   E059 : Short_Integer; pragma Import (Ada, E059, "ada__tags_E");
   E123 : Short_Integer; pragma Import (Ada, E123, "ada__streams_E");
   E075 : Short_Integer; pragma Import (Ada, E075, "interfaces__c_E");
   E077 : Short_Integer; pragma Import (Ada, E077, "interfaces__c__strings_E");
   E032 : Short_Integer; pragma Import (Ada, E032, "system__exceptions_E");
   E144 : Short_Integer; pragma Import (Ada, E144, "system__finalization_root_E");
   E142 : Short_Integer; pragma Import (Ada, E142, "ada__finalization_E");
   E158 : Short_Integer; pragma Import (Ada, E158, "system__storage_pools_E");
   E152 : Short_Integer; pragma Import (Ada, E152, "system__finalization_masters_E");
   E164 : Short_Integer; pragma Import (Ada, E164, "system__storage_pools__subpools_E");
   E095 : Short_Integer; pragma Import (Ada, E095, "system__task_info_E");
   E280 : Short_Integer; pragma Import (Ada, E280, "ada__synchronous_task_control_E");
   E296 : Short_Integer; pragma Import (Ada, E296, "ada__calendar_E");
   E160 : Short_Integer; pragma Import (Ada, E160, "system__pool_global_E");
   E150 : Short_Integer; pragma Import (Ada, E150, "system__file_control_block_E");
   E134 : Short_Integer; pragma Import (Ada, E134, "ada__streams__stream_io_E");
   E140 : Short_Integer; pragma Import (Ada, E140, "system__file_io_E");
   E201 : Short_Integer; pragma Import (Ada, E201, "gnat__sockets_E");
   E208 : Short_Integer; pragma Import (Ada, E208, "system__pool_size_E");
   E024 : Short_Integer; pragma Import (Ada, E024, "system__secondary_stack_E");
   E206 : Short_Integer; pragma Import (Ada, E206, "gnat__sockets__thin_common_E");
   E204 : Short_Integer; pragma Import (Ada, E204, "gnat__sockets__thin_E");
   E132 : Short_Integer; pragma Import (Ada, E132, "system__strings__stream_ops_E");
   E264 : Short_Integer; pragma Import (Ada, E264, "system__tasking__initialization_E");
   E067 : Short_Integer; pragma Import (Ada, E067, "system__tasking__protected_objects_E");
   E216 : Short_Integer; pragma Import (Ada, E216, "ada__real_time_E");
   E188 : Short_Integer; pragma Import (Ada, E188, "ada__text_io_E");
   E266 : Short_Integer; pragma Import (Ada, E266, "system__tasking__protected_objects__entries_E");
   E270 : Short_Integer; pragma Import (Ada, E270, "system__tasking__queuing_E");
   E276 : Short_Integer; pragma Import (Ada, E276, "system__tasking__stages_E");
   E172 : Short_Integer; pragma Import (Ada, E172, "dns_types_E");
   E197 : Short_Integer; pragma Import (Ada, E197, "dns_network_E");
   E222 : Short_Integer; pragma Import (Ada, E222, "dns_network_receive_E");
   E214 : Short_Integer; pragma Import (Ada, E214, "multitask_process_dns_request_E");
   E224 : Short_Integer; pragma Import (Ada, E224, "protected_spark_io_05_E");
   E199 : Short_Integer; pragma Import (Ada, E199, "socket_timeout_E");
   E184 : Short_Integer; pragma Import (Ada, E184, "spark__ada__text_io_E");
   E186 : Short_Integer; pragma Import (Ada, E186, "spark__ada__text_io__not_spark_E");
   E190 : Short_Integer; pragma Import (Ada, E190, "spark_ada_command_line_E");
   E278 : Short_Integer; pragma Import (Ada, E278, "task_limit_E");
   E195 : Short_Integer; pragma Import (Ada, E195, "tcp_dns_package_E");
   E294 : Short_Integer; pragma Import (Ada, E294, "non_spark_stuff_E");
   E122 : Short_Integer; pragma Import (Ada, E122, "rr_type_E");
   E286 : Short_Integer; pragma Import (Ada, E286, "error_msgs_E");
   E128 : Short_Integer; pragma Import (Ada, E128, "rr_type__a_record_type_E");
   E129 : Short_Integer; pragma Import (Ada, E129, "rr_type__aaaa_record_type_E");
   E130 : Short_Integer; pragma Import (Ada, E130, "rr_type__cname_record_type_E");
   E167 : Short_Integer; pragma Import (Ada, E167, "rr_type__dnskey_record_type_E");
   E168 : Short_Integer; pragma Import (Ada, E168, "rr_type__mx_record_type_E");
   E169 : Short_Integer; pragma Import (Ada, E169, "rr_type__ns_record_type_E");
   E170 : Short_Integer; pragma Import (Ada, E170, "rr_type__nsec_record_type_E");
   E177 : Short_Integer; pragma Import (Ada, E177, "rr_type__ptr_record_type_E");
   E178 : Short_Integer; pragma Import (Ada, E178, "rr_type__rrsig_record_type_E");
   E292 : Short_Integer; pragma Import (Ada, E292, "parser_utilities_E");
   E298 : Short_Integer; pragma Import (Ada, E298, "process_first_line_of_record_E");
   E179 : Short_Integer; pragma Import (Ada, E179, "rr_type__soa_record_type_E");
   E180 : Short_Integer; pragma Import (Ada, E180, "rr_type__srv_record_type_E");
   E005 : Short_Integer; pragma Import (Ada, E005, "dns_table_pkg_E");
   E220 : Short_Integer; pragma Import (Ada, E220, "process_dns_request_E");
   E282 : Short_Integer; pragma Import (Ada, E282, "udp_dns_package_E");
   E284 : Short_Integer; pragma Import (Ada, E284, "zone_file_io_E");
   E300 : Short_Integer; pragma Import (Ada, E300, "zone_file_parser_E");

   Local_Priority_Specific_Dispatching : constant String := "";
   Local_Interrupt_States : constant String := "";

   Is_Elaborated : Boolean := False;

   procedure finalize_library is
   begin
      declare
         procedure F1;
         pragma Import (Ada, F1, "udp_dns_package__finalize_body");
      begin
         E282 := E282 - 1;
         F1;
      end;
      declare
         procedure F2;
         pragma Import (Ada, F2, "tcp_dns_package__finalize_body");
      begin
         E195 := E195 - 1;
         F2;
      end;
      E005 := E005 - 1;
      declare
         procedure F3;
         pragma Import (Ada, F3, "dns_table_pkg__finalize_spec");
      begin
         F3;
      end;
      declare
         procedure F4;
         pragma Import (Ada, F4, "rr_type__srv_record_type__finalize_spec");
      begin
         E180 := E180 - 1;
         F4;
      end;
      declare
         procedure F5;
         pragma Import (Ada, F5, "rr_type__soa_record_type__finalize_spec");
      begin
         E179 := E179 - 1;
         F5;
      end;
      declare
         procedure F6;
         pragma Import (Ada, F6, "rr_type__rrsig_record_type__finalize_spec");
      begin
         E178 := E178 - 1;
         F6;
      end;
      declare
         procedure F7;
         pragma Import (Ada, F7, "rr_type__ptr_record_type__finalize_spec");
      begin
         E177 := E177 - 1;
         F7;
      end;
      declare
         procedure F8;
         pragma Import (Ada, F8, "rr_type__nsec_record_type__finalize_spec");
      begin
         E170 := E170 - 1;
         F8;
      end;
      declare
         procedure F9;
         pragma Import (Ada, F9, "rr_type__ns_record_type__finalize_spec");
      begin
         E169 := E169 - 1;
         F9;
      end;
      declare
         procedure F10;
         pragma Import (Ada, F10, "rr_type__mx_record_type__finalize_spec");
      begin
         E168 := E168 - 1;
         F10;
      end;
      declare
         procedure F11;
         pragma Import (Ada, F11, "rr_type__dnskey_record_type__finalize_spec");
      begin
         E167 := E167 - 1;
         F11;
      end;
      declare
         procedure F12;
         pragma Import (Ada, F12, "rr_type__cname_record_type__finalize_spec");
      begin
         E130 := E130 - 1;
         F12;
      end;
      declare
         procedure F13;
         pragma Import (Ada, F13, "rr_type__aaaa_record_type__finalize_spec");
      begin
         E129 := E129 - 1;
         F13;
      end;
      declare
         procedure F14;
         pragma Import (Ada, F14, "rr_type__a_record_type__finalize_spec");
      begin
         E128 := E128 - 1;
         F14;
      end;
      E122 := E122 - 1;
      declare
         procedure F15;
         pragma Import (Ada, F15, "rr_type__finalize_spec");
      begin
         F15;
      end;
      E224 := E224 - 1;
      declare
         procedure F16;
         pragma Import (Ada, F16, "protected_spark_io_05__finalize_spec");
      begin
         F16;
      end;
      E266 := E266 - 1;
      declare
         procedure F17;
         pragma Import (Ada, F17, "system__tasking__protected_objects__entries__finalize_spec");
      begin
         F17;
      end;
      E188 := E188 - 1;
      declare
         procedure F18;
         pragma Import (Ada, F18, "ada__text_io__finalize_spec");
      begin
         F18;
      end;
      declare
         procedure F19;
         pragma Import (Ada, F19, "gnat__sockets__finalize_body");
      begin
         E201 := E201 - 1;
         F19;
      end;
      E152 := E152 - 1;
      E164 := E164 - 1;
      declare
         procedure F20;
         pragma Import (Ada, F20, "system__file_io__finalize_body");
      begin
         E140 := E140 - 1;
         F20;
      end;
      E208 := E208 - 1;
      declare
         procedure F21;
         pragma Import (Ada, F21, "system__pool_size__finalize_spec");
      begin
         F21;
      end;
      declare
         procedure F22;
         pragma Import (Ada, F22, "gnat__sockets__finalize_spec");
      begin
         F22;
      end;
      E134 := E134 - 1;
      declare
         procedure F23;
         pragma Import (Ada, F23, "ada__streams__stream_io__finalize_spec");
      begin
         F23;
      end;
      declare
         procedure F24;
         pragma Import (Ada, F24, "system__file_control_block__finalize_spec");
      begin
         E150 := E150 - 1;
         F24;
      end;
      E160 := E160 - 1;
      declare
         procedure F25;
         pragma Import (Ada, F25, "system__pool_global__finalize_spec");
      begin
         F25;
      end;
      E280 := E280 - 1;
      declare
         procedure F26;
         pragma Import (Ada, F26, "ada__synchronous_task_control__finalize_spec");
      begin
         F26;
      end;
      declare
         procedure F27;
         pragma Import (Ada, F27, "system__storage_pools__subpools__finalize_spec");
      begin
         F27;
      end;
      declare
         procedure F28;
         pragma Import (Ada, F28, "system__finalization_masters__finalize_spec");
      begin
         F28;
      end;
      declare
         procedure Reraise_Library_Exception_If_Any;
            pragma Import (Ada, Reraise_Library_Exception_If_Any, "__gnat_reraise_library_exception_if_any");
      begin
         Reraise_Library_Exception_If_Any;
      end;
   end finalize_library;

   procedure adafinal is
      procedure s_stalib_adafinal;
      pragma Import (C, s_stalib_adafinal, "system__standard_library__adafinal");
   begin
      if not Is_Elaborated then
         return;
      end if;
      Is_Elaborated := False;
      s_stalib_adafinal;
   end adafinal;

   type No_Param_Proc is access procedure;

   procedure adainit is
      Main_Priority : Integer;
      pragma Import (C, Main_Priority, "__gl_main_priority");
      Time_Slice_Value : Integer;
      pragma Import (C, Time_Slice_Value, "__gl_time_slice_val");
      WC_Encoding : Character;
      pragma Import (C, WC_Encoding, "__gl_wc_encoding");
      Locking_Policy : Character;
      pragma Import (C, Locking_Policy, "__gl_locking_policy");
      Queuing_Policy : Character;
      pragma Import (C, Queuing_Policy, "__gl_queuing_policy");
      Task_Dispatching_Policy : Character;
      pragma Import (C, Task_Dispatching_Policy, "__gl_task_dispatching_policy");
      Priority_Specific_Dispatching : System.Address;
      pragma Import (C, Priority_Specific_Dispatching, "__gl_priority_specific_dispatching");
      Num_Specific_Dispatching : Integer;
      pragma Import (C, Num_Specific_Dispatching, "__gl_num_specific_dispatching");
      Main_CPU : Integer;
      pragma Import (C, Main_CPU, "__gl_main_cpu");
      Interrupt_States : System.Address;
      pragma Import (C, Interrupt_States, "__gl_interrupt_states");
      Num_Interrupt_States : Integer;
      pragma Import (C, Num_Interrupt_States, "__gl_num_interrupt_states");
      Unreserve_All_Interrupts : Integer;
      pragma Import (C, Unreserve_All_Interrupts, "__gl_unreserve_all_interrupts");
      Detect_Blocking : Integer;
      pragma Import (C, Detect_Blocking, "__gl_detect_blocking");
      Default_Stack_Size : Integer;
      pragma Import (C, Default_Stack_Size, "__gl_default_stack_size");
      Leap_Seconds_Support : Integer;
      pragma Import (C, Leap_Seconds_Support, "__gl_leap_seconds_support");

      procedure Install_Handler;
      pragma Import (C, Install_Handler, "__gnat_install_handler");

      Handler_Installed : Integer;
      pragma Import (C, Handler_Installed, "__gnat_handler_installed");

      Finalize_Library_Objects : No_Param_Proc;
      pragma Import (C, Finalize_Library_Objects, "__gnat_finalize_library_objects");
   begin
      if Is_Elaborated then
         return;
      end if;
      Is_Elaborated := True;
      Main_Priority := 0;
      Time_Slice_Value := -1;
      WC_Encoding := 'b';
      Locking_Policy := ' ';
      Queuing_Policy := ' ';
      Task_Dispatching_Policy := ' ';
      System.Restrictions.Run_Time_Restrictions :=
        (Set =>
          (False, False, False, False, False, False, False, False,
           False, False, False, False, False, False, False, False,
           False, False, False, False, False, False, False, False,
           False, False, False, False, False, False, False, False,
           False, False, False, False, False, False, False, False,
           False, False, False, False, False, False, False, False,
           False, False, False, False, False, False, False, False,
           False, False, False, False, False, False, False, False,
           False, False, False, False, False, True, False, False,
           False, False, False, False, False, False, False, False,
           False, False, False),
         Value => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
         Violated =>
          (False, False, False, True, True, False, False, True,
           False, False, True, True, True, True, False, False,
           True, False, False, True, True, False, True, True,
           True, True, True, True, False, False, True, False,
           True, False, False, True, False, True, True, False,
           False, False, True, False, False, False, True, False,
           True, True, False, False, False, True, False, True,
           True, True, False, False, True, False, False, True,
           False, True, True, False, True, True, True, False,
           True, False, False, False, False, False, True, True,
           False, True, False),
         Count => (0, 0, 0, 0, 0, 1, 3, 0, 5, 0),
         Unknown => (False, False, False, False, False, False, True, False, True, False));
      Priority_Specific_Dispatching :=
        Local_Priority_Specific_Dispatching'Address;
      Num_Specific_Dispatching := 0;
      Main_CPU := -1;
      Interrupt_States := Local_Interrupt_States'Address;
      Num_Interrupt_States := 0;
      Unreserve_All_Interrupts := 0;
      Detect_Blocking := 0;
      Default_Stack_Size := -1;
      Leap_Seconds_Support := 0;

      if Handler_Installed = 0 then
         Install_Handler;
      end if;

      Finalize_Library_Objects := finalize_library'access;

      System.Soft_Links'Elab_Spec;
      System.Fat_Flt'Elab_Spec;
      E255 := E255 + 1;
      System.Fat_Llf'Elab_Spec;
      E231 := E231 + 1;
      System.Exception_Table'Elab_Body;
      E014 := E014 + 1;
      Ada.Io_Exceptions'Elab_Spec;
      E126 := E126 + 1;
      Ada.Strings'Elab_Spec;
      E011 := E011 + 1;
      Ada.Strings.Maps'Elab_Spec;
      Ada.Strings.Maps.Constants'Elab_Spec;
      E057 := E057 + 1;
      Ada.Tags'Elab_Spec;
      Ada.Streams'Elab_Spec;
      E123 := E123 + 1;
      Interfaces.C'Elab_Spec;
      Interfaces.C.Strings'Elab_Spec;
      System.Exceptions'Elab_Spec;
      E032 := E032 + 1;
      System.Finalization_Root'Elab_Spec;
      E144 := E144 + 1;
      Ada.Finalization'Elab_Spec;
      E142 := E142 + 1;
      System.Storage_Pools'Elab_Spec;
      E158 := E158 + 1;
      System.Finalization_Masters'Elab_Spec;
      System.Storage_Pools.Subpools'Elab_Spec;
      System.Task_Info'Elab_Spec;
      E095 := E095 + 1;
      Ada.Synchronous_Task_Control'Elab_Spec;
      E280 := E280 + 1;
      Ada.Calendar'Elab_Spec;
      Ada.Calendar'Elab_Body;
      E296 := E296 + 1;
      System.Pool_Global'Elab_Spec;
      E160 := E160 + 1;
      System.File_Control_Block'Elab_Spec;
      E150 := E150 + 1;
      Ada.Streams.Stream_Io'Elab_Spec;
      E134 := E134 + 1;
      Gnat.Sockets'Elab_Spec;
      System.Pool_Size'Elab_Spec;
      E208 := E208 + 1;
      System.File_Io'Elab_Body;
      E140 := E140 + 1;
      E164 := E164 + 1;
      System.Finalization_Masters'Elab_Body;
      E152 := E152 + 1;
      E077 := E077 + 1;
      E075 := E075 + 1;
      Ada.Tags'Elab_Body;
      E059 := E059 + 1;
      E053 := E053 + 1;
      System.Soft_Links'Elab_Body;
      E020 := E020 + 1;
      System.Os_Lib'Elab_Body;
      E147 := E147 + 1;
      System.Secondary_Stack'Elab_Body;
      E024 := E024 + 1;
      Gnat.Sockets.Thin_Common'Elab_Spec;
      E206 := E206 + 1;
      Gnat.Sockets.Thin'Elab_Body;
      E204 := E204 + 1;
      Gnat.Sockets'Elab_Body;
      E201 := E201 + 1;
      System.Strings.Stream_Ops'Elab_Body;
      E132 := E132 + 1;
      System.Tasking.Initialization'Elab_Body;
      E264 := E264 + 1;
      System.Tasking.Protected_Objects'Elab_Body;
      E067 := E067 + 1;
      Ada.Real_Time'Elab_Spec;
      Ada.Real_Time'Elab_Body;
      E216 := E216 + 1;
      Ada.Text_Io'Elab_Spec;
      Ada.Text_Io'Elab_Body;
      E188 := E188 + 1;
      System.Tasking.Protected_Objects.Entries'Elab_Spec;
      E266 := E266 + 1;
      System.Tasking.Queuing'Elab_Body;
      E270 := E270 + 1;
      System.Tasking.Stages'Elab_Body;
      E276 := E276 + 1;
      E172 := E172 + 1;
      E222 := E222 + 1;
      Protected_Spark_Io_05'Elab_Spec;
      Protected_Spark_Io_05'Elab_Body;
      E224 := E224 + 1;
      E199 := E199 + 1;
      Dns_Network'Elab_Body;
      E197 := E197 + 1;
      E186 := E186 + 1;
      SPARK.ADA.TEXT_IO'ELAB_BODY;
      E184 := E184 + 1;
      E190 := E190 + 1;
      E278 := E278 + 1;
      Non_Spark_Stuff'Elab_Body;
      E294 := E294 + 1;
      Rr_Type'Elab_Spec;
      E122 := E122 + 1;
      Rr_Type.A_Record_Type'Elab_Spec;
      E128 := E128 + 1;
      Rr_Type.Aaaa_Record_Type'Elab_Spec;
      E129 := E129 + 1;
      Rr_Type.Cname_Record_Type'Elab_Spec;
      E130 := E130 + 1;
      Rr_Type.Dnskey_Record_Type'Elab_Spec;
      E167 := E167 + 1;
      Rr_Type.Mx_Record_Type'Elab_Spec;
      E168 := E168 + 1;
      Rr_Type.Ns_Record_Type'Elab_Spec;
      E169 := E169 + 1;
      Rr_Type.Nsec_Record_Type'Elab_Spec;
      E170 := E170 + 1;
      Error_Msgs'Elab_Body;
      E286 := E286 + 1;
      Rr_Type.Ptr_Record_Type'Elab_Spec;
      E177 := E177 + 1;
      Rr_Type.Rrsig_Record_Type'Elab_Spec;
      E178 := E178 + 1;
      Rr_Type.Soa_Record_Type'Elab_Spec;
      E179 := E179 + 1;
      E292 := E292 + 1;
      Rr_Type.Srv_Record_Type'Elab_Spec;
      E180 := E180 + 1;
      dns_table_pkg'elab_spec;
      E005 := E005 + 1;
      E220 := E220 + 1;
      Multitask_Process_Dns_Request'Elab_Body;
      E214 := E214 + 1;
      Tcp_Dns_Package'Elab_Body;
      E195 := E195 + 1;
      Udp_Dns_Package'Elab_Body;
      E282 := E282 + 1;
      E300 := E300 + 1;
      E284 := E284 + 1;
      E298 := E298 + 1;
   end adainit;

   procedure Ada_Main_Program;
   pragma Import (Ada, Ada_Main_Program, "_ada_spark_dns_main");

   function main
     (argc : Integer;
      argv : System.Address;
      envp : System.Address)
      return Integer
   is
      procedure Initialize (Addr : System.Address);
      pragma Import (C, Initialize, "__gnat_initialize");

      procedure Finalize;
      pragma Import (C, Finalize, "__gnat_finalize");
      SEH : aliased array (1 .. 2) of Integer;

      Ensure_Reference : aliased System.Address := Ada_Main_Program_Name'Address;
      pragma Volatile (Ensure_Reference);

   begin
      gnat_argc := argc;
      gnat_argv := argv;
      gnat_envp := envp;

      Initialize (SEH'Address);
      adainit;
      Ada_Main_Program;
      adafinal;
      Finalize;
      return (gnat_exit_status);
   end;

--  BEGIN Object file/option list
   --   .\dns_types.o
   --   .\dns_network_receive.o
   --   .\protected_spark_io_05.o
   --   .\socket_timeout.o
   --   .\dns_network.o
   --   .\spark.o
   --   .\spark-ada.o
   --   .\spark-ada-text_io-not_spark.o
   --   .\spark-ada-text_io.o
   --   .\spark_ada_command_line.o
   --   .\task_limit.o
   --   .\unsigned_types.o
   --   .\non_spark_stuff.o
   --   .\rr_type.o
   --   .\rr_type-a_record_type.o
   --   .\rr_type-aaaa_record_type.o
   --   .\rr_type-cname_record_type.o
   --   .\rr_type-dnskey_record_type.o
   --   .\rr_type-mx_record_type.o
   --   .\rr_type-ns_record_type.o
   --   .\rr_type-nsec_record_type.o
   --   .\error_msgs.o
   --   .\rr_type-ptr_record_type.o
   --   .\rr_type-rrsig_record_type.o
   --   .\rr_type-soa_record_type.o
   --   .\parser_utilities.o
   --   .\rr_type-srv_record_type.o
   --   .\dns_table_pkg.o
   --   .\process_dns_request.o
   --   .\multitask_process_dns_request.o
   --   .\tcp_dns_package.o
   --   .\udp_dns_package.o
   --   .\spark_dns_main.o
   --   .\zone_file_parser.o
   --   .\zone_file_io.o
   --   .\process_first_line_of_record.o
   --   -L.\
   --   -LC:\Users\MARTIN~2.CAR\DOCUME~1\DARPA-~2\trunk\
   --   -Lc:\spark\2012\lib\spark\
   --   -Lc:\spark\2012\lib\spark\current\
   --   -LC:/GNAT/2013/lib/gcc/i686-pc-mingw32/4.7.4/adalib/
   --   -static
   --   -lgnarl
   --   -lgnat
   --   -lws2_32
   --   -Xlinker
   --   --stack=0x200000,0x1000
   --   -mthreads
   --   -Wl,--stack=0x2000000
--  END Object file/option list

end ada_main;
