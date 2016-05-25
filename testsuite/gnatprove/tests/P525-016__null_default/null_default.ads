package Null_Default with SPARK_Mode is

   generic
      with procedure P (X : in out Integer) is null;
   package Gen is
   end Gen;

   package Inst is new Gen;

end Null_Default;
