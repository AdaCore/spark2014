with System.Regexp;       use System.Regexp;

package body Adadir is
   pragma SPARK_Mode (Off);

   type Search_Data is record
      Pattern       : Regexp;
   end record;

end Adadir;
