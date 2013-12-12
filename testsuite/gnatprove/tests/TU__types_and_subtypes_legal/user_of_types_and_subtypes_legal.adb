package body User_Of_Types_And_Subtypes_Legal
  with SPARK_Mode
is
   function Same_As_Next (N : Node) return Boolean is
     (Get_Data (N) = Get_Data (Get_Next (N)));
end User_Of_Types_And_Subtypes_Legal;
