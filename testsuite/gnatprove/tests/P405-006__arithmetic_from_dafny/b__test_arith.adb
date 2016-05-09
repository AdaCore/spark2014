pragma Ada_95;
pragma Warnings (Off);
pragma Source_File_Name (ada_main, Spec_File_Name => "b__test_arith.ads");
pragma Source_File_Name (ada_main, Body_File_Name => "b__test_arith.adb");
pragma Suppress (Overflow_Check);

package body ada_main is

   E19 : Short_Integer; pragma Import (Ada, E19, "system__soft_links_E");
   E29 : Short_Integer; pragma Import (Ada, E29, "system__exception_table_E");
   E31 : Short_Integer; pragma Import (Ada, E31, "system__exceptions_E");
   E11 : Short_Integer; pragma Import (Ada, E11, "system__assertions_E");
   E23 : Short_Integer; pragma Import (Ada, E23, "system__secondary_stack_E");
   E09 : Short_Integer; pragma Import (Ada, E09, "spark__arithmetic_lemmas_E");

   Local_Priority_Specific_Dispatching : constant String := "";
   Local_Interrupt_States : constant String := "";

   Is_Elaborated : Boolean := False;

   procedure adafinal is
      procedure s_stalib_adafinal;
      pragma Import (C, s_stalib_adafinal, "system__standard_library__adafinal");

      procedure Runtime_Finalize;
      pragma Import (C, Runtime_Finalize, "__gnat_runtime_finalize");

   begin
      if not Is_Elaborated then
         return;
      end if;
      Is_Elaborated := False;
      Runtime_Finalize;
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
      Bind_Env_Addr : System.Address;
      pragma Import (C, Bind_Env_Addr, "__gl_bind_env_addr");

      procedure Runtime_Initialize (Install_Handler : Integer);
      pragma Import (C, Runtime_Initialize, "__gnat_runtime_initialize");

      Finalize_Library_Objects : No_Param_Proc;
      pragma Import (C, Finalize_Library_Objects, "__gnat_finalize_library_objects");
   begin
      if Is_Elaborated then
         return;
      end if;
      Is_Elaborated := True;
      Main_Priority := -1;
      Time_Slice_Value := -1;
      WC_Encoding := 'b';
      Locking_Policy := ' ';
      Queuing_Policy := ' ';
      Task_Dispatching_Policy := ' ';
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

      Runtime_Initialize (1);

      Finalize_Library_Objects := null;

      System.Soft_Links'Elab_Spec;
      System.Exception_Table'Elab_Body;
      E29 := E29 + 1;
      System.Exceptions'Elab_Spec;
      E31 := E31 + 1;
      System.Assertions'Elab_Spec;
      E11 := E11 + 1;
      System.Soft_Links'Elab_Body;
      E19 := E19 + 1;
      System.Secondary_Stack'Elab_Body;
      E23 := E23 + 1;
      E09 := E09 + 1;
   end adainit;

   procedure Ada_Main_Program;
   pragma Import (Ada, Ada_Main_Program, "_ada_test_arith");

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
   --   /Users/moy/spark2014/install/lib/gnat/spark.o
   --   /Users/moy/spark2014/install/lib/gnat/spark-arithmetic_lemmas.o
   --   /Users/moy/spark2014/install/lib/gnat/spark-integer_arithmetic_lemmas.o
   --   /Users/moy/spark2014/testsuite/gnatprove/tests/P405-006__arithmetic_from_dafny/div_lemmas.o
   --   /Users/moy/spark2014/testsuite/gnatprove/tests/P405-006__arithmetic_from_dafny/mod_lemmas.o
   --   /Users/moy/spark2014/testsuite/gnatprove/tests/P405-006__arithmetic_from_dafny/mul_lemmas.o
   --   /Users/moy/spark2014/testsuite/gnatprove/tests/P405-006__arithmetic_from_dafny/test_arith.o
   --   -L/Users/moy/spark2014/testsuite/gnatprove/tests/P405-006__arithmetic_from_dafny/
   --   -L/Users/moy/spark2014/testsuite/gnatprove/tests/P405-006__arithmetic_from_dafny/
   --   -L/Users/moy/spark2014/install/lib/gnat/
   --   -L/Users/moy/install/sandbox/x86_64-darwin/gnat/install/lib/gcc/x86_64-apple-darwin14.5.0/4.9.4/adalib/
   --   -static
   --   -lgnat
--  END Object file/option list   

end ada_main;
