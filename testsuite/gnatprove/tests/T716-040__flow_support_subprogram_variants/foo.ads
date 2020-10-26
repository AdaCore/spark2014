package Foo with SPARK_Mode is

   procedure Recursive_Proc_W_Variant (X : Natural) with
     Subprogram_Variant => (Decreases => X);

end Foo;
