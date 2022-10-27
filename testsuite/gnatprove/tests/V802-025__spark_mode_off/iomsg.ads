with Interfaces;
package Iomsg
  with SPARK_Mode => On
is
   type Extended_Flags_T is private;
   function "and"
     (L, R : Extended_Flags_T)
      return Extended_Flags_T with
      Inline;
private
   pragma SPARK_Mode (Off);
   type Extended_Flags_T is new Interfaces.Unsigned_32;
end;
