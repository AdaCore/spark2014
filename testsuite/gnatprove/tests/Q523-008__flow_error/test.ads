pragma SPARK_Mode;

with Global;

package Test
is
   function Test return Integer
   is (Global.Val)
     with Global => null;

end Test;
