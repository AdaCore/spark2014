with Ada.Containers.Formal_Vectors;

package body T is

   function Extract_Mod return Value is
      package Inst is new Ada.Containers.Formal_Vectors (Index_Type => Positive, Element_Type => Boolean, "=" => "=");
   begin
      return Value'First;
   end Extract_Mod;

end T;
