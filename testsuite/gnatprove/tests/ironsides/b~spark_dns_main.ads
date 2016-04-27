pragma Ada_95;
with System;
package ada_main is
   pragma Warnings (Off);

   gnat_argc : Integer;
   gnat_argv : System.Address;
   gnat_envp : System.Address;

   pragma Import (C, gnat_argc);
   pragma Import (C, gnat_argv);
   pragma Import (C, gnat_envp);

   gnat_exit_status : Integer;
   pragma Import (C, gnat_exit_status);

   GNAT_Version : constant String :=
                    "GNAT Version: GPL 2013 (20130314)" & ASCII.NUL;
   pragma Export (C, GNAT_Version, "__gnat_version");

   Ada_Main_Program_Name : constant String := "_ada_spark_dns_main" & ASCII.NUL;
   pragma Export (C, Ada_Main_Program_Name, "__gnat_ada_main_program_name");

   procedure adainit;
   pragma Export (C, adainit, "adainit");

   procedure adafinal;
   pragma Export (C, adafinal, "adafinal");

   function main
     (argc : Integer;
      argv : System.Address;
      envp : System.Address)
      return Integer;
   pragma Export (C, main, "main");

   type Version_32 is mod 2 ** 32;
   u00001 : constant Version_32 := 16#ee7ee11c#;
   pragma Export (C, u00001, "spark_dns_mainB");
   u00002 : constant Version_32 := 16#3935bd10#;
   pragma Export (C, u00002, "system__standard_libraryB");
   u00003 : constant Version_32 := 16#51a8eec5#;
   pragma Export (C, u00003, "system__standard_libraryS");
   u00004 : constant Version_32 := 16#76885304#;
   pragma Export (C, u00004, "dns_table_pkgB");
   u00005 : constant Version_32 := 16#4465aa2f#;
   pragma Export (C, u00005, "dns_table_pkgS");
   u00006 : constant Version_32 := 16#3ffc8e18#;
   pragma Export (C, u00006, "adaS");
   u00007 : constant Version_32 := 16#12c24a43#;
   pragma Export (C, u00007, "ada__charactersS");
   u00008 : constant Version_32 := 16#6239f067#;
   pragma Export (C, u00008, "ada__characters__handlingB");
   u00009 : constant Version_32 := 16#3006d996#;
   pragma Export (C, u00009, "ada__characters__handlingS");
   u00010 : constant Version_32 := 16#051b1b7b#;
   pragma Export (C, u00010, "ada__characters__latin_1S");
   u00011 : constant Version_32 := 16#af50e98f#;
   pragma Export (C, u00011, "ada__stringsS");
   u00012 : constant Version_32 := 16#5fc8ae56#;
   pragma Export (C, u00012, "systemS");
   u00013 : constant Version_32 := 16#7b9f0bae#;
   pragma Export (C, u00013, "system__exception_tableB");
   u00014 : constant Version_32 := 16#cea672f3#;
   pragma Export (C, u00014, "system__exception_tableS");
   u00015 : constant Version_32 := 16#5665ab64#;
   pragma Export (C, u00015, "system__htableB");
   u00016 : constant Version_32 := 16#dc60e058#;
   pragma Export (C, u00016, "system__htableS");
   u00017 : constant Version_32 := 16#8b7dad61#;
   pragma Export (C, u00017, "system__string_hashB");
   u00018 : constant Version_32 := 16#795476c2#;
   pragma Export (C, u00018, "system__string_hashS");
   u00019 : constant Version_32 := 16#0071025c#;
   pragma Export (C, u00019, "system__soft_linksB");
   u00020 : constant Version_32 := 16#3293d48b#;
   pragma Export (C, u00020, "system__soft_linksS");
   u00021 : constant Version_32 := 16#27940d94#;
   pragma Export (C, u00021, "system__parametersB");
   u00022 : constant Version_32 := 16#e92aa296#;
   pragma Export (C, u00022, "system__parametersS");
   u00023 : constant Version_32 := 16#17775d6d#;
   pragma Export (C, u00023, "system__secondary_stackB");
   u00024 : constant Version_32 := 16#4ba689f8#;
   pragma Export (C, u00024, "system__secondary_stackS");
   u00025 : constant Version_32 := 16#ace32e1e#;
   pragma Export (C, u00025, "system__storage_elementsB");
   u00026 : constant Version_32 := 16#a505d3ce#;
   pragma Export (C, u00026, "system__storage_elementsS");
   u00027 : constant Version_32 := 16#5ea2bd7b#;
   pragma Export (C, u00027, "ada__exceptionsB");
   u00028 : constant Version_32 := 16#6380a30f#;
   pragma Export (C, u00028, "ada__exceptionsS");
   u00029 : constant Version_32 := 16#16173147#;
   pragma Export (C, u00029, "ada__exceptions__last_chance_handlerB");
   u00030 : constant Version_32 := 16#1f42fb5e#;
   pragma Export (C, u00030, "ada__exceptions__last_chance_handlerS");
   u00031 : constant Version_32 := 16#aad75561#;
   pragma Export (C, u00031, "system__exceptionsB");
   u00032 : constant Version_32 := 16#533666e1#;
   pragma Export (C, u00032, "system__exceptionsS");
   u00033 : constant Version_32 := 16#010db1dc#;
   pragma Export (C, u00033, "system__exceptions_debugB");
   u00034 : constant Version_32 := 16#67b88b82#;
   pragma Export (C, u00034, "system__exceptions_debugS");
   u00035 : constant Version_32 := 16#b012ff50#;
   pragma Export (C, u00035, "system__img_intB");
   u00036 : constant Version_32 := 16#5d134e94#;
   pragma Export (C, u00036, "system__img_intS");
   u00037 : constant Version_32 := 16#dc8e33ed#;
   pragma Export (C, u00037, "system__tracebackB");
   u00038 : constant Version_32 := 16#3e4f7a23#;
   pragma Export (C, u00038, "system__tracebackS");
   u00039 : constant Version_32 := 16#907d882f#;
   pragma Export (C, u00039, "system__wch_conB");
   u00040 : constant Version_32 := 16#e023806b#;
   pragma Export (C, u00040, "system__wch_conS");
   u00041 : constant Version_32 := 16#22fed88a#;
   pragma Export (C, u00041, "system__wch_stwB");
   u00042 : constant Version_32 := 16#cd32ac6a#;
   pragma Export (C, u00042, "system__wch_stwS");
   u00043 : constant Version_32 := 16#617a40f2#;
   pragma Export (C, u00043, "system__wch_cnvB");
   u00044 : constant Version_32 := 16#fedd06bd#;
   pragma Export (C, u00044, "system__wch_cnvS");
   u00045 : constant Version_32 := 16#cb4a8015#;
   pragma Export (C, u00045, "interfacesS");
   u00046 : constant Version_32 := 16#75729fba#;
   pragma Export (C, u00046, "system__wch_jisB");
   u00047 : constant Version_32 := 16#aaaf9da9#;
   pragma Export (C, u00047, "system__wch_jisS");
   u00048 : constant Version_32 := 16#ada34a87#;
   pragma Export (C, u00048, "system__traceback_entriesB");
   u00049 : constant Version_32 := 16#0de94017#;
   pragma Export (C, u00049, "system__traceback_entriesS");
   u00050 : constant Version_32 := 16#4f750b3b#;
   pragma Export (C, u00050, "system__stack_checkingB");
   u00051 : constant Version_32 := 16#fc6a127a#;
   pragma Export (C, u00051, "system__stack_checkingS");
   u00052 : constant Version_32 := 16#96e9c1e7#;
   pragma Export (C, u00052, "ada__strings__mapsB");
   u00053 : constant Version_32 := 16#24318e4c#;
   pragma Export (C, u00053, "ada__strings__mapsS");
   u00054 : constant Version_32 := 16#d7ba84a5#;
   pragma Export (C, u00054, "system__bit_opsB");
   u00055 : constant Version_32 := 16#c30e4013#;
   pragma Export (C, u00055, "system__bit_opsS");
   u00056 : constant Version_32 := 16#3529f220#;
   pragma Export (C, u00056, "system__unsigned_typesS");
   u00057 : constant Version_32 := 16#7a69aa90#;
   pragma Export (C, u00057, "ada__strings__maps__constantsS");
   u00058 : constant Version_32 := 16#afd62b40#;
   pragma Export (C, u00058, "ada__tagsB");
   u00059 : constant Version_32 := 16#f6fc5406#;
   pragma Export (C, u00059, "ada__tagsS");
   u00060 : constant Version_32 := 16#79817c71#;
   pragma Export (C, u00060, "system__val_unsB");
   u00061 : constant Version_32 := 16#25811f1b#;
   pragma Export (C, u00061, "system__val_unsS");
   u00062 : constant Version_32 := 16#aea309ed#;
   pragma Export (C, u00062, "system__val_utilB");
   u00063 : constant Version_32 := 16#f36818a8#;
   pragma Export (C, u00063, "system__val_utilS");
   u00064 : constant Version_32 := 16#b7fa72e7#;
   pragma Export (C, u00064, "system__case_utilB");
   u00065 : constant Version_32 := 16#f2d4cede#;
   pragma Export (C, u00065, "system__case_utilS");
   u00066 : constant Version_32 := 16#bb8952df#;
   pragma Export (C, u00066, "system__tasking__protected_objectsB");
   u00067 : constant Version_32 := 16#09cb1bb5#;
   pragma Export (C, u00067, "system__tasking__protected_objectsS");
   u00068 : constant Version_32 := 16#1151ce70#;
   pragma Export (C, u00068, "system__soft_links__taskingB");
   u00069 : constant Version_32 := 16#6ac0d6d0#;
   pragma Export (C, u00069, "system__soft_links__taskingS");
   u00070 : constant Version_32 := 16#17d21067#;
   pragma Export (C, u00070, "ada__exceptions__is_null_occurrenceB");
   u00071 : constant Version_32 := 16#d832eaef#;
   pragma Export (C, u00071, "ada__exceptions__is_null_occurrenceS");
   u00072 : constant Version_32 := 16#4ff85dba#;
   pragma Export (C, u00072, "system__task_primitivesS");
   u00073 : constant Version_32 := 16#cf49590f#;
   pragma Export (C, u00073, "system__os_interfaceS");
   u00074 : constant Version_32 := 16#769e25e6#;
   pragma Export (C, u00074, "interfaces__cB");
   u00075 : constant Version_32 := 16#29899d4e#;
   pragma Export (C, u00075, "interfaces__cS");
   u00076 : constant Version_32 := 16#507533cc#;
   pragma Export (C, u00076, "interfaces__c__stringsB");
   u00077 : constant Version_32 := 16#603c1c44#;
   pragma Export (C, u00077, "interfaces__c__stringsS");
   u00078 : constant Version_32 := 16#ee4e202b#;
   pragma Export (C, u00078, "system__win32S");
   u00079 : constant Version_32 := 16#07176fd5#;
   pragma Export (C, u00079, "system__task_primitives__operationsB");
   u00080 : constant Version_32 := 16#074ed32a#;
   pragma Export (C, u00080, "system__task_primitives__operationsS");
   u00081 : constant Version_32 := 16#6f001a54#;
   pragma Export (C, u00081, "system__exp_unsB");
   u00082 : constant Version_32 := 16#08e5518a#;
   pragma Export (C, u00082, "system__exp_unsS");
   u00083 : constant Version_32 := 16#1b28662b#;
   pragma Export (C, u00083, "system__float_controlB");
   u00084 : constant Version_32 := 16#bf34ed6a#;
   pragma Export (C, u00084, "system__float_controlS");
   u00085 : constant Version_32 := 16#1826115c#;
   pragma Export (C, u00085, "system__interrupt_managementB");
   u00086 : constant Version_32 := 16#a0a25a36#;
   pragma Export (C, u00086, "system__interrupt_managementS");
   u00087 : constant Version_32 := 16#f65595cf#;
   pragma Export (C, u00087, "system__multiprocessorsB");
   u00088 : constant Version_32 := 16#67643125#;
   pragma Export (C, u00088, "system__multiprocessorsS");
   u00089 : constant Version_32 := 16#d950d226#;
   pragma Export (C, u00089, "system__os_primitivesB");
   u00090 : constant Version_32 := 16#ef19227f#;
   pragma Export (C, u00090, "system__os_primitivesS");
   u00091 : constant Version_32 := 16#863f9596#;
   pragma Export (C, u00091, "system__task_lockB");
   u00092 : constant Version_32 := 16#3e429938#;
   pragma Export (C, u00092, "system__task_lockS");
   u00093 : constant Version_32 := 16#48cfbab9#;
   pragma Export (C, u00093, "system__win32__extS");
   u00094 : constant Version_32 := 16#5052be8c#;
   pragma Export (C, u00094, "system__task_infoB");
   u00095 : constant Version_32 := 16#3ffea91d#;
   pragma Export (C, u00095, "system__task_infoS");
   u00096 : constant Version_32 := 16#91dfc027#;
   pragma Export (C, u00096, "system__taskingB");
   u00097 : constant Version_32 := 16#d83d5e83#;
   pragma Export (C, u00097, "system__taskingS");
   u00098 : constant Version_32 := 16#083296f2#;
   pragma Export (C, u00098, "system__stack_usageB");
   u00099 : constant Version_32 := 16#7ccb26a7#;
   pragma Export (C, u00099, "system__stack_usageS");
   u00100 : constant Version_32 := 16#36e568f7#;
   pragma Export (C, u00100, "system__crtlS");
   u00101 : constant Version_32 := 16#d7aac20c#;
   pragma Export (C, u00101, "system__ioB");
   u00102 : constant Version_32 := 16#c18a5919#;
   pragma Export (C, u00102, "system__ioS");
   u00103 : constant Version_32 := 16#1692df3b#;
   pragma Export (C, u00103, "system__tasking__debugB");
   u00104 : constant Version_32 := 16#f32cb5c6#;
   pragma Export (C, u00104, "system__tasking__debugS");
   u00105 : constant Version_32 := 16#39591e91#;
   pragma Export (C, u00105, "system__concat_2B");
   u00106 : constant Version_32 := 16#a4185caa#;
   pragma Export (C, u00106, "system__concat_2S");
   u00107 : constant Version_32 := 16#ae97ef6c#;
   pragma Export (C, u00107, "system__concat_3B");
   u00108 : constant Version_32 := 16#29e2ac3c#;
   pragma Export (C, u00108, "system__concat_3S");
   u00109 : constant Version_32 := 16#c9fdc962#;
   pragma Export (C, u00109, "system__concat_6B");
   u00110 : constant Version_32 := 16#98025b42#;
   pragma Export (C, u00110, "system__concat_6S");
   u00111 : constant Version_32 := 16#def1dd00#;
   pragma Export (C, u00111, "system__concat_5B");
   u00112 : constant Version_32 := 16#4ff160f7#;
   pragma Export (C, u00112, "system__concat_5S");
   u00113 : constant Version_32 := 16#3493e6c0#;
   pragma Export (C, u00113, "system__concat_4B");
   u00114 : constant Version_32 := 16#5d974de8#;
   pragma Export (C, u00114, "system__concat_4S");
   u00115 : constant Version_32 := 16#1eab0e09#;
   pragma Export (C, u00115, "system__img_enum_newB");
   u00116 : constant Version_32 := 16#d8cf65a6#;
   pragma Export (C, u00116, "system__img_enum_newS");
   u00117 : constant Version_32 := 16#194ccd7b#;
   pragma Export (C, u00117, "system__img_unsB");
   u00118 : constant Version_32 := 16#aaddced7#;
   pragma Export (C, u00118, "system__img_unsS");
   u00119 : constant Version_32 := 16#ee80728a#;
   pragma Export (C, u00119, "system__tracesB");
   u00120 : constant Version_32 := 16#add5c6fc#;
   pragma Export (C, u00120, "system__tracesS");
   u00121 : constant Version_32 := 16#9ce6e57d#;
   pragma Export (C, u00121, "rr_typeB");
   u00122 : constant Version_32 := 16#f6134437#;
   pragma Export (C, u00122, "rr_typeS");
   u00123 : constant Version_32 := 16#1358602f#;
   pragma Export (C, u00123, "ada__streamsS");
   u00124 : constant Version_32 := 16#a6e358bc#;
   pragma Export (C, u00124, "system__stream_attributesB");
   u00125 : constant Version_32 := 16#e89b4b3f#;
   pragma Export (C, u00125, "system__stream_attributesS");
   u00126 : constant Version_32 := 16#b46168d5#;
   pragma Export (C, u00126, "ada__io_exceptionsS");
   u00127 : constant Version_32 := 16#dd57bff3#;
   pragma Export (C, u00127, "unsigned_typesS");
   u00128 : constant Version_32 := 16#d03c8901#;
   pragma Export (C, u00128, "rr_type__a_record_typeS");
   u00129 : constant Version_32 := 16#c3bf41bf#;
   pragma Export (C, u00129, "rr_type__aaaa_record_typeS");
   u00130 : constant Version_32 := 16#6b807061#;
   pragma Export (C, u00130, "rr_type__cname_record_typeS");
   u00131 : constant Version_32 := 16#ce0e2acb#;
   pragma Export (C, u00131, "system__strings__stream_opsB");
   u00132 : constant Version_32 := 16#8453d1c6#;
   pragma Export (C, u00132, "system__strings__stream_opsS");
   u00133 : constant Version_32 := 16#9d848be4#;
   pragma Export (C, u00133, "ada__streams__stream_ioB");
   u00134 : constant Version_32 := 16#31db4e88#;
   pragma Export (C, u00134, "ada__streams__stream_ioS");
   u00135 : constant Version_32 := 16#e0b7a7e8#;
   pragma Export (C, u00135, "interfaces__c_streamsB");
   u00136 : constant Version_32 := 16#95ad191f#;
   pragma Export (C, u00136, "interfaces__c_streamsS");
   u00137 : constant Version_32 := 16#5de653db#;
   pragma Export (C, u00137, "system__communicationB");
   u00138 : constant Version_32 := 16#aae38b10#;
   pragma Export (C, u00138, "system__communicationS");
   u00139 : constant Version_32 := 16#228a5436#;
   pragma Export (C, u00139, "system__file_ioB");
   u00140 : constant Version_32 := 16#ce89cf71#;
   pragma Export (C, u00140, "system__file_ioS");
   u00141 : constant Version_32 := 16#8cbe6205#;
   pragma Export (C, u00141, "ada__finalizationB");
   u00142 : constant Version_32 := 16#22e22193#;
   pragma Export (C, u00142, "ada__finalizationS");
   u00143 : constant Version_32 := 16#95817ed8#;
   pragma Export (C, u00143, "system__finalization_rootB");
   u00144 : constant Version_32 := 16#103addc6#;
   pragma Export (C, u00144, "system__finalization_rootS");
   u00145 : constant Version_32 := 16#d6bc4ecc#;
   pragma Export (C, u00145, "system__crtl__runtimeS");
   u00146 : constant Version_32 := 16#f6ee85e9#;
   pragma Export (C, u00146, "system__os_libB");
   u00147 : constant Version_32 := 16#89dce9aa#;
   pragma Export (C, u00147, "system__os_libS");
   u00148 : constant Version_32 := 16#4cd8aca0#;
   pragma Export (C, u00148, "system__stringsB");
   u00149 : constant Version_32 := 16#e822e492#;
   pragma Export (C, u00149, "system__stringsS");
   u00150 : constant Version_32 := 16#782cc428#;
   pragma Export (C, u00150, "system__file_control_blockS");
   u00151 : constant Version_32 := 16#91d2300e#;
   pragma Export (C, u00151, "system__finalization_mastersB");
   u00152 : constant Version_32 := 16#353d027a#;
   pragma Export (C, u00152, "system__finalization_mastersS");
   u00153 : constant Version_32 := 16#57a37a42#;
   pragma Export (C, u00153, "system__address_imageB");
   u00154 : constant Version_32 := 16#fe24336c#;
   pragma Export (C, u00154, "system__address_imageS");
   u00155 : constant Version_32 := 16#7268f812#;
   pragma Export (C, u00155, "system__img_boolB");
   u00156 : constant Version_32 := 16#aa11dfbd#;
   pragma Export (C, u00156, "system__img_boolS");
   u00157 : constant Version_32 := 16#a7a37cb6#;
   pragma Export (C, u00157, "system__storage_poolsB");
   u00158 : constant Version_32 := 16#8c66b13b#;
   pragma Export (C, u00158, "system__storage_poolsS");
   u00159 : constant Version_32 := 16#ba5d60c7#;
   pragma Export (C, u00159, "system__pool_globalB");
   u00160 : constant Version_32 := 16#d56df0a6#;
   pragma Export (C, u00160, "system__pool_globalS");
   u00161 : constant Version_32 := 16#742a8355#;
   pragma Export (C, u00161, "system__memoryB");
   u00162 : constant Version_32 := 16#95431243#;
   pragma Export (C, u00162, "system__memoryS");
   u00163 : constant Version_32 := 16#1fd820b1#;
   pragma Export (C, u00163, "system__storage_pools__subpoolsB");
   u00164 : constant Version_32 := 16#951e0de9#;
   pragma Export (C, u00164, "system__storage_pools__subpoolsS");
   u00165 : constant Version_32 := 16#1777d351#;
   pragma Export (C, u00165, "system__storage_pools__subpools__finalizationB");
   u00166 : constant Version_32 := 16#12aaf1de#;
   pragma Export (C, u00166, "system__storage_pools__subpools__finalizationS");
   u00167 : constant Version_32 := 16#87a20243#;
   pragma Export (C, u00167, "rr_type__dnskey_record_typeS");
   u00168 : constant Version_32 := 16#2b493902#;
   pragma Export (C, u00168, "rr_type__mx_record_typeS");
   u00169 : constant Version_32 := 16#b7bf1392#;
   pragma Export (C, u00169, "rr_type__ns_record_typeS");
   u00170 : constant Version_32 := 16#74364172#;
   pragma Export (C, u00170, "rr_type__nsec_record_typeS");
   u00171 : constant Version_32 := 16#395ecc26#;
   pragma Export (C, u00171, "dns_typesB");
   u00172 : constant Version_32 := 16#8fc81469#;
   pragma Export (C, u00172, "dns_typesS");
   u00173 : constant Version_32 := 16#fd2ad2f1#;
   pragma Export (C, u00173, "gnatS");
   u00174 : constant Version_32 := 16#45efda4c#;
   pragma Export (C, u00174, "gnat__byte_swappingB");
   u00175 : constant Version_32 := 16#06306a9e#;
   pragma Export (C, u00175, "gnat__byte_swappingS");
   u00176 : constant Version_32 := 16#2654da16#;
   pragma Export (C, u00176, "system__byte_swappingS");
   u00177 : constant Version_32 := 16#d1d36f03#;
   pragma Export (C, u00177, "rr_type__ptr_record_typeS");
   u00178 : constant Version_32 := 16#55f27b75#;
   pragma Export (C, u00178, "rr_type__rrsig_record_typeS");
   u00179 : constant Version_32 := 16#d31c829b#;
   pragma Export (C, u00179, "rr_type__soa_record_typeS");
   u00180 : constant Version_32 := 16#488cccec#;
   pragma Export (C, u00180, "rr_type__srv_record_typeS");
   u00181 : constant Version_32 := 16#99ec3c77#;
   pragma Export (C, u00181, "sparkS");
   u00182 : constant Version_32 := 16#7227bb35#;
   pragma Export (C, u00182, "spark__adaS");
   u00183 : constant Version_32 := 16#6fc657a5#;
   pragma Export (C, u00183, "spark__ada__text_ioB");
   u00184 : constant Version_32 := 16#f3896d65#;
   pragma Export (C, u00184, "spark__ada__text_ioS");
   u00185 : constant Version_32 := 16#f31aa3a5#;
   pragma Export (C, u00185, "spark__ada__text_io__not_sparkB");
   u00186 : constant Version_32 := 16#9b085e0c#;
   pragma Export (C, u00186, "spark__ada__text_io__not_sparkS");
   u00187 : constant Version_32 := 16#421d3150#;
   pragma Export (C, u00187, "ada__text_ioB");
   u00188 : constant Version_32 := 16#152cee1e#;
   pragma Export (C, u00188, "ada__text_ioS");
   u00189 : constant Version_32 := 16#54b72bb3#;
   pragma Export (C, u00189, "spark_ada_command_lineB");
   u00190 : constant Version_32 := 16#22719490#;
   pragma Export (C, u00190, "spark_ada_command_lineS");
   u00191 : constant Version_32 := 16#988a5eb6#;
   pragma Export (C, u00191, "ada__command_lineB");
   u00192 : constant Version_32 := 16#df5044bd#;
   pragma Export (C, u00192, "ada__command_lineS");
   u00193 : constant Version_32 := 16#3ff16a6d#;
   pragma Export (C, u00193, "gnat__os_libS");
   u00194 : constant Version_32 := 16#705da679#;
   pragma Export (C, u00194, "tcp_dns_packageB");
   u00195 : constant Version_32 := 16#807d6e4b#;
   pragma Export (C, u00195, "tcp_dns_packageS");
   u00196 : constant Version_32 := 16#77b798c8#;
   pragma Export (C, u00196, "dns_networkB");
   u00197 : constant Version_32 := 16#b397e21b#;
   pragma Export (C, u00197, "dns_networkS");
   u00198 : constant Version_32 := 16#2e682382#;
   pragma Export (C, u00198, "socket_timeoutB");
   u00199 : constant Version_32 := 16#8e2dd597#;
   pragma Export (C, u00199, "socket_timeoutS");
   u00200 : constant Version_32 := 16#ba30556c#;
   pragma Export (C, u00200, "gnat__socketsB");
   u00201 : constant Version_32 := 16#c1654bca#;
   pragma Export (C, u00201, "gnat__socketsS");
   u00202 : constant Version_32 := 16#01027cb8#;
   pragma Export (C, u00202, "gnat__sockets__linker_optionsS");
   u00203 : constant Version_32 := 16#e41c2dad#;
   pragma Export (C, u00203, "gnat__sockets__thinB");
   u00204 : constant Version_32 := 16#e6561a98#;
   pragma Export (C, u00204, "gnat__sockets__thinS");
   u00205 : constant Version_32 := 16#0a2632e6#;
   pragma Export (C, u00205, "gnat__sockets__thin_commonB");
   u00206 : constant Version_32 := 16#a458fed4#;
   pragma Export (C, u00206, "gnat__sockets__thin_commonS");
   u00207 : constant Version_32 := 16#17f3840e#;
   pragma Export (C, u00207, "system__pool_sizeB");
   u00208 : constant Version_32 := 16#43063bbf#;
   pragma Export (C, u00208, "system__pool_sizeS");
   u00209 : constant Version_32 := 16#c31442ce#;
   pragma Export (C, u00209, "system__val_intB");
   u00210 : constant Version_32 := 16#176d8469#;
   pragma Export (C, u00210, "system__val_intS");
   u00211 : constant Version_32 := 16#c674770c#;
   pragma Export (C, u00211, "system__os_constantsS");
   u00212 : constant Version_32 := 16#5656832b#;
   pragma Export (C, u00212, "gnat__sockets__constantsS");
   u00213 : constant Version_32 := 16#529eb2ca#;
   pragma Export (C, u00213, "multitask_process_dns_requestB");
   u00214 : constant Version_32 := 16#1d4019e8#;
   pragma Export (C, u00214, "multitask_process_dns_requestS");
   u00215 : constant Version_32 := 16#28c4f46d#;
   pragma Export (C, u00215, "ada__real_timeB");
   u00216 : constant Version_32 := 16#41de19c7#;
   pragma Export (C, u00216, "ada__real_timeS");
   u00217 : constant Version_32 := 16#aa574b29#;
   pragma Export (C, u00217, "system__arith_64B");
   u00218 : constant Version_32 := 16#d4cf8bb1#;
   pragma Export (C, u00218, "system__arith_64S");
   u00219 : constant Version_32 := 16#7b934eaf#;
   pragma Export (C, u00219, "process_dns_requestB");
   u00220 : constant Version_32 := 16#e6740152#;
   pragma Export (C, u00220, "process_dns_requestS");
   u00221 : constant Version_32 := 16#8347336d#;
   pragma Export (C, u00221, "dns_network_receiveB");
   u00222 : constant Version_32 := 16#944b75bb#;
   pragma Export (C, u00222, "dns_network_receiveS");
   u00223 : constant Version_32 := 16#a6c2b761#;
   pragma Export (C, u00223, "protected_spark_io_05B");
   u00224 : constant Version_32 := 16#3a6ef3fb#;
   pragma Export (C, u00224, "protected_spark_io_05S");
   u00225 : constant Version_32 := 16#d5f9759f#;
   pragma Export (C, u00225, "ada__text_io__float_auxB");
   u00226 : constant Version_32 := 16#f854caf5#;
   pragma Export (C, u00226, "ada__text_io__float_auxS");
   u00227 : constant Version_32 := 16#cd6ba629#;
   pragma Export (C, u00227, "ada__text_io__generic_auxB");
   u00228 : constant Version_32 := 16#a6c327d3#;
   pragma Export (C, u00228, "ada__text_io__generic_auxS");
   u00229 : constant Version_32 := 16#6d0081c3#;
   pragma Export (C, u00229, "system__img_realB");
   u00230 : constant Version_32 := 16#9860ffb4#;
   pragma Export (C, u00230, "system__img_realS");
   u00231 : constant Version_32 := 16#80f37066#;
   pragma Export (C, u00231, "system__fat_llfS");
   u00232 : constant Version_32 := 16#06417083#;
   pragma Export (C, u00232, "system__img_lluB");
   u00233 : constant Version_32 := 16#7ce0f2e3#;
   pragma Export (C, u00233, "system__img_lluS");
   u00234 : constant Version_32 := 16#0fb8c821#;
   pragma Export (C, u00234, "system__powten_tableS");
   u00235 : constant Version_32 := 16#8ff77155#;
   pragma Export (C, u00235, "system__val_realB");
   u00236 : constant Version_32 := 16#a1e1d947#;
   pragma Export (C, u00236, "system__val_realS");
   u00237 : constant Version_32 := 16#0be1b996#;
   pragma Export (C, u00237, "system__exn_llfB");
   u00238 : constant Version_32 := 16#de4cb0b9#;
   pragma Export (C, u00238, "system__exn_llfS");
   u00239 : constant Version_32 := 16#f6fdca1c#;
   pragma Export (C, u00239, "ada__text_io__integer_auxB");
   u00240 : constant Version_32 := 16#b9793d30#;
   pragma Export (C, u00240, "ada__text_io__integer_auxS");
   u00241 : constant Version_32 := 16#ef6c8032#;
   pragma Export (C, u00241, "system__img_biuB");
   u00242 : constant Version_32 := 16#f30b7a6d#;
   pragma Export (C, u00242, "system__img_biuS");
   u00243 : constant Version_32 := 16#10618bf9#;
   pragma Export (C, u00243, "system__img_llbB");
   u00244 : constant Version_32 := 16#b2cc6a93#;
   pragma Export (C, u00244, "system__img_llbS");
   u00245 : constant Version_32 := 16#9777733a#;
   pragma Export (C, u00245, "system__img_lliB");
   u00246 : constant Version_32 := 16#4e87fb87#;
   pragma Export (C, u00246, "system__img_lliS");
   u00247 : constant Version_32 := 16#f931f062#;
   pragma Export (C, u00247, "system__img_llwB");
   u00248 : constant Version_32 := 16#1ba04905#;
   pragma Export (C, u00248, "system__img_llwS");
   u00249 : constant Version_32 := 16#b532ff4e#;
   pragma Export (C, u00249, "system__img_wiuB");
   u00250 : constant Version_32 := 16#9d4afdff#;
   pragma Export (C, u00250, "system__img_wiuS");
   u00251 : constant Version_32 := 16#d3757657#;
   pragma Export (C, u00251, "system__val_lliB");
   u00252 : constant Version_32 := 16#c5ec48f6#;
   pragma Export (C, u00252, "system__val_lliS");
   u00253 : constant Version_32 := 16#25c21d28#;
   pragma Export (C, u00253, "system__val_lluB");
   u00254 : constant Version_32 := 16#4fdba552#;
   pragma Export (C, u00254, "system__val_lluS");
   u00255 : constant Version_32 := 16#dc11d781#;
   pragma Export (C, u00255, "system__fat_fltS");
   u00256 : constant Version_32 := 16#7dbbd31d#;
   pragma Export (C, u00256, "text_ioS");
   u00257 : constant Version_32 := 16#195cdc00#;
   pragma Export (C, u00257, "system__tasking__rendezvousB");
   u00258 : constant Version_32 := 16#592e9c02#;
   pragma Export (C, u00258, "system__tasking__rendezvousS");
   u00259 : constant Version_32 := 16#386436bc#;
   pragma Export (C, u00259, "system__restrictionsB");
   u00260 : constant Version_32 := 16#fd243b13#;
   pragma Export (C, u00260, "system__restrictionsS");
   u00261 : constant Version_32 := 16#3b094f8a#;
   pragma Export (C, u00261, "system__tasking__entry_callsB");
   u00262 : constant Version_32 := 16#837d42fa#;
   pragma Export (C, u00262, "system__tasking__entry_callsS");
   u00263 : constant Version_32 := 16#a4cc7b44#;
   pragma Export (C, u00263, "system__tasking__initializationB");
   u00264 : constant Version_32 := 16#9468d5af#;
   pragma Export (C, u00264, "system__tasking__initializationS");
   u00265 : constant Version_32 := 16#8b7a9f50#;
   pragma Export (C, u00265, "system__tasking__protected_objects__entriesB");
   u00266 : constant Version_32 := 16#4d64e3b6#;
   pragma Export (C, u00266, "system__tasking__protected_objects__entriesS");
   u00267 : constant Version_32 := 16#47da7ff7#;
   pragma Export (C, u00267, "system__tasking__protected_objects__operationsB");
   u00268 : constant Version_32 := 16#a9cb954d#;
   pragma Export (C, u00268, "system__tasking__protected_objects__operationsS");
   u00269 : constant Version_32 := 16#7b8939c7#;
   pragma Export (C, u00269, "system__tasking__queuingB");
   u00270 : constant Version_32 := 16#5b69ac57#;
   pragma Export (C, u00270, "system__tasking__queuingS");
   u00271 : constant Version_32 := 16#11a73c38#;
   pragma Export (C, u00271, "system__tasking__utilitiesB");
   u00272 : constant Version_32 := 16#53d3f317#;
   pragma Export (C, u00272, "system__tasking__utilitiesS");
   u00273 : constant Version_32 := 16#bd6fc52e#;
   pragma Export (C, u00273, "system__traces__taskingB");
   u00274 : constant Version_32 := 16#55cf3c43#;
   pragma Export (C, u00274, "system__traces__taskingS");
   u00275 : constant Version_32 := 16#b3acec93#;
   pragma Export (C, u00275, "system__tasking__stagesB");
   u00276 : constant Version_32 := 16#79eb9051#;
   pragma Export (C, u00276, "system__tasking__stagesS");
   u00277 : constant Version_32 := 16#9fb84414#;
   pragma Export (C, u00277, "task_limitB");
   u00278 : constant Version_32 := 16#81b197a8#;
   pragma Export (C, u00278, "task_limitS");
   u00279 : constant Version_32 := 16#ad0c29e8#;
   pragma Export (C, u00279, "ada__synchronous_task_controlB");
   u00280 : constant Version_32 := 16#d3b94b4d#;
   pragma Export (C, u00280, "ada__synchronous_task_controlS");
   u00281 : constant Version_32 := 16#b2351600#;
   pragma Export (C, u00281, "udp_dns_packageB");
   u00282 : constant Version_32 := 16#96bda124#;
   pragma Export (C, u00282, "udp_dns_packageS");
   u00283 : constant Version_32 := 16#7de2dfd7#;
   pragma Export (C, u00283, "zone_file_ioB");
   u00284 : constant Version_32 := 16#3adb2569#;
   pragma Export (C, u00284, "zone_file_ioS");
   u00285 : constant Version_32 := 16#1812770d#;
   pragma Export (C, u00285, "error_msgsB");
   u00286 : constant Version_32 := 16#0d191d8b#;
   pragma Export (C, u00286, "error_msgsS");
   u00287 : constant Version_32 := 16#f64b89a4#;
   pragma Export (C, u00287, "ada__integer_text_ioB");
   u00288 : constant Version_32 := 16#f1daf268#;
   pragma Export (C, u00288, "ada__integer_text_ioS");
   u00289 : constant Version_32 := 16#a347755d#;
   pragma Export (C, u00289, "ada__text_io__modular_auxB");
   u00290 : constant Version_32 := 16#534ccfb2#;
   pragma Export (C, u00290, "ada__text_io__modular_auxS");
   u00291 : constant Version_32 := 16#5666b144#;
   pragma Export (C, u00291, "parser_utilitiesB");
   u00292 : constant Version_32 := 16#e4416e7b#;
   pragma Export (C, u00292, "parser_utilitiesS");
   u00293 : constant Version_32 := 16#b668d498#;
   pragma Export (C, u00293, "non_spark_stuffB");
   u00294 : constant Version_32 := 16#7963463b#;
   pragma Export (C, u00294, "non_spark_stuffS");
   u00295 : constant Version_32 := 16#8ba0787e#;
   pragma Export (C, u00295, "ada__calendarB");
   u00296 : constant Version_32 := 16#e791e294#;
   pragma Export (C, u00296, "ada__calendarS");
   u00297 : constant Version_32 := 16#2bf1db51#;
   pragma Export (C, u00297, "process_first_line_of_recordB");
   u00298 : constant Version_32 := 16#2806452b#;
   pragma Export (C, u00298, "process_first_line_of_recordS");
   u00299 : constant Version_32 := 16#67d7fa7a#;
   pragma Export (C, u00299, "zone_file_parserB");
   u00300 : constant Version_32 := 16#d1add036#;
   pragma Export (C, u00300, "zone_file_parserS");
   --  BEGIN ELABORATION ORDER
   --  ada%s
   --  ada.characters%s
   --  ada.characters.handling%s
   --  ada.characters.latin_1%s
   --  ada.command_line%s
   --  gnat%s
   --  interfaces%s
   --  system%s
   --  gnat.byte_swapping%s
   --  system.arith_64%s
   --  system.byte_swapping%s
   --  gnat.byte_swapping%b
   --  system.case_util%s
   --  system.case_util%b
   --  system.exn_llf%s
   --  system.exn_llf%b
   --  system.float_control%s
   --  system.float_control%b
   --  system.htable%s
   --  system.img_bool%s
   --  system.img_bool%b
   --  system.img_enum_new%s
   --  system.img_enum_new%b
   --  system.img_int%s
   --  system.img_int%b
   --  system.img_lli%s
   --  system.img_lli%b
   --  system.img_real%s
   --  system.io%s
   --  system.io%b
   --  system.multiprocessors%s
   --  system.os_primitives%s
   --  system.parameters%s
   --  system.parameters%b
   --  system.crtl%s
   --  interfaces.c_streams%s
   --  interfaces.c_streams%b
   --  system.powten_table%s
   --  system.restrictions%s
   --  system.restrictions%b
   --  system.standard_library%s
   --  system.exceptions_debug%s
   --  system.exceptions_debug%b
   --  system.storage_elements%s
   --  system.storage_elements%b
   --  system.stack_checking%s
   --  system.stack_checking%b
   --  system.stack_usage%s
   --  system.stack_usage%b
   --  system.string_hash%s
   --  system.string_hash%b
   --  system.htable%b
   --  system.strings%s
   --  system.strings%b
   --  system.os_lib%s
   --  gnat.os_lib%s
   --  system.task_lock%s
   --  system.traceback_entries%s
   --  system.traceback_entries%b
   --  ada.exceptions%s
   --  system.arith_64%b
   --  ada.exceptions.is_null_occurrence%s
   --  ada.exceptions.is_null_occurrence%b
   --  system.soft_links%s
   --  system.task_lock%b
   --  system.traces%s
   --  system.traces%b
   --  system.unsigned_types%s
   --  system.exp_uns%s
   --  system.exp_uns%b
   --  system.fat_flt%s
   --  system.fat_llf%s
   --  system.img_biu%s
   --  system.img_biu%b
   --  system.img_llb%s
   --  system.img_llb%b
   --  system.img_llu%s
   --  system.img_llu%b
   --  system.img_llw%s
   --  system.img_llw%b
   --  system.img_uns%s
   --  system.img_uns%b
   --  system.img_real%b
   --  system.img_wiu%s
   --  system.img_wiu%b
   --  system.val_int%s
   --  system.val_lli%s
   --  system.val_llu%s
   --  system.val_real%s
   --  system.val_uns%s
   --  system.val_util%s
   --  system.val_util%b
   --  system.val_uns%b
   --  system.val_real%b
   --  system.val_llu%b
   --  system.val_lli%b
   --  system.val_int%b
   --  system.wch_con%s
   --  system.wch_con%b
   --  system.wch_cnv%s
   --  system.wch_jis%s
   --  system.wch_jis%b
   --  system.wch_cnv%b
   --  system.wch_stw%s
   --  system.wch_stw%b
   --  ada.exceptions.last_chance_handler%s
   --  ada.exceptions.last_chance_handler%b
   --  system.address_image%s
   --  system.bit_ops%s
   --  system.bit_ops%b
   --  system.concat_2%s
   --  system.concat_2%b
   --  system.concat_3%s
   --  system.concat_3%b
   --  system.concat_4%s
   --  system.concat_4%b
   --  system.concat_5%s
   --  system.concat_5%b
   --  system.concat_6%s
   --  system.concat_6%b
   --  system.exception_table%s
   --  system.exception_table%b
   --  ada.io_exceptions%s
   --  ada.strings%s
   --  ada.strings.maps%s
   --  ada.strings.maps.constants%s
   --  ada.tags%s
   --  ada.streams%s
   --  interfaces.c%s
   --  system.multiprocessors%b
   --  interfaces.c.strings%s
   --  system.communication%s
   --  system.communication%b
   --  system.crtl.runtime%s
   --  system.exceptions%s
   --  system.exceptions%b
   --  system.finalization_root%s
   --  system.finalization_root%b
   --  ada.finalization%s
   --  ada.finalization%b
   --  system.os_constants%s
   --  system.storage_pools%s
   --  system.storage_pools%b
   --  system.finalization_masters%s
   --  system.storage_pools.subpools%s
   --  system.storage_pools.subpools.finalization%s
   --  system.storage_pools.subpools.finalization%b
   --  system.stream_attributes%s
   --  system.stream_attributes%b
   --  system.win32%s
   --  system.os_interface%s
   --  system.interrupt_management%s
   --  system.interrupt_management%b
   --  system.task_info%s
   --  system.task_info%b
   --  system.task_primitives%s
   --  ada.synchronous_task_control%s
   --  system.tasking%s
   --  system.task_primitives.operations%s
   --  system.tasking%b
   --  ada.synchronous_task_control%b
   --  system.tasking.debug%s
   --  system.tasking.debug%b
   --  system.traces.tasking%s
   --  system.traces.tasking%b
   --  system.win32.ext%s
   --  system.task_primitives.operations%b
   --  system.os_primitives%b
   --  ada.calendar%s
   --  ada.calendar%b
   --  system.memory%s
   --  system.memory%b
   --  system.standard_library%b
   --  system.pool_global%s
   --  system.pool_global%b
   --  system.file_control_block%s
   --  ada.streams.stream_io%s
   --  system.file_io%s
   --  ada.streams.stream_io%b
   --  gnat.sockets%s
   --  gnat.sockets.constants%s
   --  gnat.sockets.linker_options%s
   --  system.pool_size%s
   --  system.pool_size%b
   --  system.secondary_stack%s
   --  system.file_io%b
   --  system.storage_pools.subpools%b
   --  system.finalization_masters%b
   --  interfaces.c.strings%b
   --  interfaces.c%b
   --  ada.tags%b
   --  ada.strings.maps%b
   --  system.soft_links%b
   --  system.os_lib%b
   --  ada.command_line%b
   --  ada.characters.handling%b
   --  system.secondary_stack%b
   --  system.address_image%b
   --  gnat.sockets.thin_common%s
   --  gnat.sockets.thin_common%b
   --  gnat.sockets.thin%s
   --  gnat.sockets.thin%b
   --  gnat.sockets%b
   --  system.soft_links.tasking%s
   --  system.soft_links.tasking%b
   --  system.strings.stream_ops%s
   --  system.strings.stream_ops%b
   --  system.tasking.entry_calls%s
   --  system.tasking.initialization%s
   --  system.tasking.initialization%b
   --  system.tasking.protected_objects%s
   --  system.tasking.protected_objects%b
   --  system.tasking.utilities%s
   --  system.traceback%s
   --  ada.exceptions%b
   --  system.traceback%b
   --  ada.real_time%s
   --  ada.real_time%b
   --  ada.text_io%s
   --  ada.text_io%b
   --  ada.text_io.float_aux%s
   --  ada.text_io.generic_aux%s
   --  ada.text_io.generic_aux%b
   --  ada.text_io.float_aux%b
   --  ada.text_io.integer_aux%s
   --  ada.text_io.integer_aux%b
   --  ada.integer_text_io%s
   --  ada.integer_text_io%b
   --  ada.text_io.modular_aux%s
   --  ada.text_io.modular_aux%b
   --  system.tasking.protected_objects.entries%s
   --  system.tasking.protected_objects.entries%b
   --  system.tasking.queuing%s
   --  system.tasking.queuing%b
   --  system.tasking.utilities%b
   --  system.tasking.rendezvous%s
   --  system.tasking.protected_objects.operations%s
   --  system.tasking.protected_objects.operations%b
   --  system.tasking.rendezvous%b
   --  system.tasking.entry_calls%b
   --  system.tasking.stages%s
   --  system.tasking.stages%b
   --  text_io%s
   --  dns_types%s
   --  dns_types%b
   --  dns_network%s
   --  dns_network_receive%s
   --  dns_network_receive%b
   --  multitask_process_dns_request%s
   --  protected_spark_io_05%s
   --  protected_spark_io_05%b
   --  socket_timeout%s
   --  socket_timeout%b
   --  dns_network%b
   --  spark%s
   --  spark.ada%s
   --  spark.ada.text_io%s
   --  spark.ada.text_io.not_spark%s
   --  spark.ada.text_io.not_spark%b
   --  spark.ada.text_io%b
   --  spark_ada_command_line%s
   --  spark_ada_command_line%b
   --  task_limit%s
   --  task_limit%b
   --  tcp_dns_package%s
   --  unsigned_types%s
   --  non_spark_stuff%s
   --  non_spark_stuff%b
   --  rr_type%s
   --  rr_type%b
   --  error_msgs%s
   --  rr_type.a_record_type%s
   --  rr_type.aaaa_record_type%s
   --  rr_type.cname_record_type%s
   --  rr_type.dnskey_record_type%s
   --  rr_type.mx_record_type%s
   --  rr_type.ns_record_type%s
   --  rr_type.nsec_record_type%s
   --  error_msgs%b
   --  rr_type.ptr_record_type%s
   --  rr_type.rrsig_record_type%s
   --  parser_utilities%s
   --  process_first_line_of_record%s
   --  rr_type.soa_record_type%s
   --  parser_utilities%b
   --  rr_type.srv_record_type%s
   --  dns_table_pkg%s
   --  dns_table_pkg%b
   --  process_dns_request%s
   --  process_dns_request%b
   --  multitask_process_dns_request%b
   --  tcp_dns_package%b
   --  udp_dns_package%s
   --  udp_dns_package%b
   --  zone_file_io%s
   --  spark_dns_main%b
   --  zone_file_parser%s
   --  zone_file_parser%b
   --  zone_file_io%b
   --  process_first_line_of_record%b
   --  END ELABORATION ORDER


end ada_main;
