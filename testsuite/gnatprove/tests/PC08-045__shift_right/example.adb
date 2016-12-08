pragma SPARK_Mode(On);

package body Example is

   function High_Octet(Value : in Double_Octet) return Octet is
   begin
      return Octet(Shift_Right(Value, 8));
   end High_Octet;

end Example;
