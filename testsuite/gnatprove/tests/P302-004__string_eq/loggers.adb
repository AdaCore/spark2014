with General_Strings;

package body Loggers with
SPARK_Mode
is

   function Get_Error (Object : Logger; Position : Cursor) return String is
   begin
      return General_Strings.To_String (Element (Container => Object.Error_Log,
                                                     Position  => Position));
   end Get_Error;

   function Has_Error (Object : Logger; Position : Cursor) return Boolean is
   begin
      return Has_Element (Container => Object.Error_Log,
                          Position  => Position);
   end Has_Error;

end Loggers;
