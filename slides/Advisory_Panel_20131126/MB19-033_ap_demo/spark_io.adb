with Text_IO;
package body SPARK_IO
  with SPARK_Mode => Off
is

   procedure Put_Line (S : in String)
   is
   begin
      Text_IO.Put_Line (S);
   end Put_Line;

end SPARK_IO;
