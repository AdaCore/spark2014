with SPARK.Containers.Formal.Ordered_Sets;

generic
   type Unique_Id_Type is range <>;
package Id_Manager
  with SPARK_Mode => On
is
   package Keys is new SPARK.Containers.Formal.Ordered_Sets (Unique_Id_Type);
   use Keys;

   procedure Display (Id_Key : Keys.Set);

end Id_Manager;
