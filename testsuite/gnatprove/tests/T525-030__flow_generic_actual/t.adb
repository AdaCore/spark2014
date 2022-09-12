with SPARK.Containers.Formal.Vectors;

package body T is

   function Extract_Mod return Value is
      package Inst is new SPARK.Containers.Formal.Vectors (Index_Type => Positive, Element_Type => Boolean, "=" => "=");
   begin
      return Value'First;
   end Extract_Mod;

end T;
