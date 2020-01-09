with Func;

generic
package G is
   pragma Assert (Func (0));
private
   pragma SPARK_Mode (Off);
   pragma Assert (Func (1));
end G;
