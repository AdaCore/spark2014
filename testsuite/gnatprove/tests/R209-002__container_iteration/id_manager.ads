with Ada.Containers.Formal_Ordered_Sets;
use Ada.Containers;

generic
   type Unique_Id_Type is range <>;
package Id_Manager
  with SPARK_Mode => On
is
   package Keys is new Ada.Containers.Formal_Ordered_Sets (Unique_Id_Type);
   use Keys;

   procedure Display (Id_Key : Keys.Set);

end Id_Manager;
