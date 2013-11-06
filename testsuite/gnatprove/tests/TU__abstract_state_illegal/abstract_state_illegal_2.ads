package Abstract_State_Illegal_2
  with SPARK_Mode,
       Abstract_State => S
is
   procedure P1;
private
   package Nested_Private_Package
     --  TU: 3. If an ``option_list`` contains one or more
     --  ``name_value_option`` items then they shall be the final options in
     --  the list.
     --  [This eliminates the possibility of a positional
     --  association following a named association in the property list.]
     with Abstract_State => (Pr_S with Part_Of => S,
                                       External)
   is
      procedure P2;
   end Nested_Private_Package;
end Abstract_State_Illegal_2;
