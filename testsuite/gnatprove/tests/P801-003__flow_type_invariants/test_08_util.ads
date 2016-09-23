package Test_08_Util is

   function Is_Positive_Good (N : Integer) return Boolean
   with Post => Is_Positive_Good'Result = (N >= 1);

   function Is_Positive_Bad (N : Integer) return Boolean
   with Post => Is_Positive_Bad'Result = (N >= 1);

   function Is_Positive_Ugly (N : Integer) return Boolean
   with Post => Is_Positive_Ugly'Result = (N >= 1);

end Test_08_Util;
