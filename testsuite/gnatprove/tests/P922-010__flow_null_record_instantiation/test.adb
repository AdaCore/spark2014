with My_Generic;

package body Test is

   type Null_Record_Type is record
      null;
   end record;

   package Crash is new My_Generic (T => Null_Record_Type);

end Test;
