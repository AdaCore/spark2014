with Ada.Text_IO; use Ada.Text_IO;

package body P_Print with SPARK_Mode => Off is

   procedure Print (Name : in String;
                    Y    : in T)
     with SPARK_Mode => Off
   is
   begin
      case Y.E is
         when One => Put_Line (Name & ": X1 = " & Integer'Image (Y.X1));
         when Two => Put_Line (Name & ": X1 = " & Integer'Image (Y.X1) & ", X2 = " & Integer'Image (Y.X2));
      end case;
   end Print;

end P_Print;
