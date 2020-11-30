package Foo with SPARK_Mode is

   type Boolean_Function is
     access function return Boolean;

   procedure Bar (Func : Boolean_Function) with
     Pre => Func.all;

end Foo;
