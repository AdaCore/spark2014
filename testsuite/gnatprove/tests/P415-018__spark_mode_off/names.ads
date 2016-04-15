--  This is a name table that maps strings to name_id and can recover the
--  original string.

--  Abstract state disabled due to P413-012

package Names with
   SPARK_Mode,
   Elaborate_Body,
   Abstract_State => Name_Table
is

   type Name_Id is new Natural;

end Names;
