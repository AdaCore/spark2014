package Bbool with SPARK_Mode is
   function F (B : Boolean) return Boolean is (False);
   subtype B is Boolean range F(False) .. F(True);
end Bbool;
