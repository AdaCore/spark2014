package Abstract_State_Legal
  with SPARK_Mode
is
   package Valid_Null
   --  abstract_state_list ::= null
     with Abstract_State => null
   is
   end Valid_Null;


   package State_Name
   --  abstract_state_list ::= state_name
     with Abstract_State => A
   is
   end State_Name;


   package Many_State_Names
   --  abstract_state_list ::= state_name {, state_name}
     with Abstract_State => (A, B, C)
   is
   end Many_State_Names;


   package State_Name_With_Options
   --  abstract_state_list ::= state_name_with_options
     with Abstract_State => (A with External)
   is
   end State_Name_With_Options;


   package Many_State_Names_With_Options
   --  abstract_state_list ::= state_name_with_options {, state_name_with_options}
     with Abstract_State => ((A with External),
                             (B with External => Async_Readers),
                             C,
                             (D with External => (Async_Readers,
                                                  Effective_Writes)),
                             (E with External => (Async_Writers,
                                                  Effective_Reads => True,
                                                  others          => False)),
                             (F with External => (Async_Writers => True)),
                             (G with External => (Async_Readers,
                                                  Async_Writers,
                                                  Effective_Writes)),
                             (H with External => (Async_Readers,
                                                  Async_Writers,
                                                  Effective_Reads,
                                                  others => False)),
                             (I with External => (Async_Readers,
                                                  Async_Writers)),
                             (J with External => (others => True)))
   is
   end Many_State_Names_With_Options;


   package Mixed_State_Names
   --  abstract_state_list ::= state_name, {state_name_with_options}
     with Abstract_State => (A,
                             (B with External),
                             (C with External),
                             D,
                             (E with External => Async_Readers),
                             F)
   is
   end Mixed_State_Names;


   package With_Private_Nested_Package
     with Abstract_State => S
   is
      procedure Some_Proc;
   private
      package Private_Nested_Package
        with Abstract_State => (Priv_S with Part_Of => S)
      is
         procedure Some_Other_Proc;
      end Private_Nested_Package;
   end With_Private_Nested_Package;


   package Overloaded_State_Name
     with Abstract_State => A
   is
      function A return Integer;
   end Overloaded_State_Name;
end Abstract_State_Legal;
