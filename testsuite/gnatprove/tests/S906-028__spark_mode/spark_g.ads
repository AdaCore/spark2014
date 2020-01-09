with Func;

generic
package SPARK_G with SPARK_Mode => On is
   pragma Assert (Func (0));
private
   pragma SPARK_Mode (Off);
   pragma Assert (Func (1));
end SPARK_G;
