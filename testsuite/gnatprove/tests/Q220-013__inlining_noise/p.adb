with G; pragma Elaborate_All (G);

package body P with SPARK_Mode is

   procedure Dummy is null;

   package Instance is new G;

end;
