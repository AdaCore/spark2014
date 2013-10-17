with Ada.Text_IO;
package body Print
   with SPARK_Mode => Off
is

  procedure Put (X : Integer) is
  begin
     Ada.Text_IO.Put_Line (X'Img);
  end Put;
end Print;
