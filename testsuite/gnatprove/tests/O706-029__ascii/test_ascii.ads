package Test_Ascii with SPARK_Mode is
   function Id (S : String) return String is (S);
   Concat : constant String := Id ("toto") & ASCII.NUL;
end;
