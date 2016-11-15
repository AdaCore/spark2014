with System;

package P with SPARK_Mode is

   X : System.Any_Priority := System.Any_Priority'First;

   protected PO is
      pragma Priority (X);
   end;

end;
