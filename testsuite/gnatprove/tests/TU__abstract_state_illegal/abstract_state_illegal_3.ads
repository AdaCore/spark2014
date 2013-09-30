package Abstract_State_Illegal_3
  --  TU: 4. A package_declaration or generic_package_declaration that
  --  contains a non-null Abstract_State aspect must have a completion (i.e.
  --  such a package requires a body).
  with SPARK_Mode,
       Abstract_State => State
is
end Abstract_State_Illegal_3;
