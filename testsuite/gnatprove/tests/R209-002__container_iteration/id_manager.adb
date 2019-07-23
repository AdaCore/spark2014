package body Id_Manager
  with SPARK_Mode => On
is
   procedure Display (Id_Key : Keys.Set) is
   begin
      for Unique_Id in Id_Key loop
         null;
      end loop;
      for Unique_Id of Id_Key loop
         null;
      end loop;
   end Display;

end Id_Manager;
