generic
   type Data_Type is private;

package Context
with SPARK_Mode
is
   --  any function is sufficient
   function Foo (Bar : Integer) return Integer is (Bar mod 100);
end Context;
