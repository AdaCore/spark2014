pragma SPARK_Mode (On);

package Inits_Pragma
is
   pragma Abstract_State (S);
   pragma Initializes (S);
   pragma Elaborate_Body;

   Y : Integer := 0;
end Inits_Pragma;
