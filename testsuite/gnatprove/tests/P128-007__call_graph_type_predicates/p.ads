with Ada.Dispatching;

package P
  with SPARK_Mode
is

   protected PO is
      entry E;
   end PO;

end P;
