package body Function_Depends_On_State
  with SPARK_Mode,
       Refined_State => (S       => (A, B),
                         S2      => (C, D),
                         S_Null  => null,
                         S_Null2 => null)
is
   A, B, C, D : Integer := 0;

   function F1 return Integer is (0)
     with Refined_Global  => null,
          Refined_Depends => (F1'Result => null);

   function F2 return Integer
     with Refined_Global  => null,
          Refined_Depends => (F2'Result => null)
   is
   begin
      return (0);
   end F2;

   function F3 return Integer
     with Refined_Global  => (A, B, C, D),
          Refined_Depends => (F3'Result => (A, C),
                              null      => (B, D))
   is
   begin
      pragma Assert (B = D);
      return Integer'Min (A, C);
   end F3;
end Function_Depends_On_State;
