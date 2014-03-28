package No_Inlining
  with SPARK_Mode
is

   procedure Test_Recursion (Res : out Boolean) with
     Post => Res = True;

end No_Inlining;
