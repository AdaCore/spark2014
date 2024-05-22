procedure Foo with SPARK_Mode is

   type My_Float is digits 4;
   function Eq (X, Y : My_Float) return Boolean is
     (X = Y and then My_Float'Copy_Sign (1.0, X) = My_Float'Copy_Sign (1.0, Y))
   with Annotate => (GNATprove, Logical_Equal);

   X : My_Float := +0.0;
   Y : My_Float := -0.0;
begin
   pragma Assert (Eq (X, Y)); -- @ASSERT:FAIL
end Foo;
