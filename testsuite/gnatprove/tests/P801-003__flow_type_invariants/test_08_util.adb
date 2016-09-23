with Test_08;

package body Test_08_Util is

   function Is_Positive_Good (N : Integer) return Boolean
   is
   begin
      return N >= 1;
   end Is_Positive_Good;

   function Is_Positive_Bad (N : Integer) return Boolean
   is
      X : Test_08.T2;
   begin
      return N >= 1;
   end Is_Positive_Bad;

   function Is_Positive_Ugly (N : Integer) return Boolean
   is
      X : Test_08.T1;
   begin
      return N >= 1;
   end Is_Positive_Ugly;

end Test_08_Util;
