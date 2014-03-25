package body Equality
is
   type Byte is range 0..255;

   type Array_T is array (Byte) of Byte;

   type SF_Record_T is record
      X : Array_T;
   end record;

   function L611_019_Reduced_Testcase (A, B, C, D: in SF_Record_T)
                                       return Boolean
     with Depends => (L611_019_Reduced_Testcase'Result => null,
                      null => (A, B, C, D)),
          Pre     => A.X = B.X
                       and B.X = C.X
                       and C.X = D.X,
          Post    => L611_019_Reduced_Testcase'Result = (A.X = D.X)  --  @POSTCONDITION:PASS
   is
   begin
      return True;
   end L611_019_Reduced_Testcase;

   function L611_019_Reduced_Testcase_2 (A, B, C, D: in SF_Record_T)
                                         return Boolean
     with Depends => (L611_019_Reduced_Testcase_2'Result => null,
                      null => (A, B, C, D)),
          Pre     => A.X = B.X
                       and B.X = C.X
                       and C.X = D.X
                       and (A.X = C.X or A.X /= C.X),
          Post    => L611_019_Reduced_Testcase_2'Result = (A.X = D.X)  --  @POSTCONDITION:PASS
   is
   begin
      return True;
   end L611_019_Reduced_Testcase_2;

end Equality;
