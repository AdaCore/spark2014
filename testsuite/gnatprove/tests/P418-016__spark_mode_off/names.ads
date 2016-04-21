package Names with
   SPARK_Mode,
   Abstract_State => Name_Table,
   Initializes    => Name_Table,
   Elaborate_Body
is

   type Name_Id is private;

private
   pragma SPARK_Mode (Off);

   type Name_Id is new Natural;

end Names;
