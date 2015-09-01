
package body Hnco.Test2 is
   pragma SPARK_Mode;

   procedure Add_Elements_To_Vector is
   begin
      V.Append (1);
      V.Append (2);

      pragma Assert (V.Contains (1));
      pragma Assert (V.Contains (2));
   end Add_Elements_To_Vector;

end Hnco.Test2;
