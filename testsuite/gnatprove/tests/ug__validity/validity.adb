with Ada.Unchecked_Conversion;

package body Validity with
  SPARK_Mode
is

   function Int_To_Float is new Ada.Unchecked_Conversion (Integer, Float);

   procedure Convert (X : Integer; Y : out Float) is
   begin
      pragma Assert (X'Valid);
      Y := Int_To_Float (X);
      pragma Assert (Y'Valid);
   end Convert;

end Validity;
