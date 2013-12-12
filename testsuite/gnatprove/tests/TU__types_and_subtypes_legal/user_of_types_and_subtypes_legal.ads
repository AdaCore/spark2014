with Types_And_Subtypes_Legal; use Types_And_Subtypes_Legal;

package User_Of_Types_And_Subtypes_Legal
  with SPARK_Mode
is
   function Same_As_Next (N : Node) return Boolean
     with Post =>
     (if Get_Data (N) /= Get_Data (Get_Next (N))
      then not Same_As_Next'Result
      else Same_As_Next'Result);
end User_Of_Types_And_Subtypes_Legal;
