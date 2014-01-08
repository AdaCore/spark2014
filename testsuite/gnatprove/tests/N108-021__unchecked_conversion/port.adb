with Ada.Unchecked_Conversion;
package body Port
is

   function C is new Ada.Unchecked_Conversion (U32, Integer);

   procedure Read_V1_Bad2 (X : out S1)
   is
      Tmp : U32;
   begin
      Tmp := V1Raw;
      X := S1 (C (Tmp));
   end Read_V1_Bad2;

end Port;
