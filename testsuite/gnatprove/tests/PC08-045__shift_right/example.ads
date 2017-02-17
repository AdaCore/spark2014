pragma SPARK_Mode(On);

package Example is

   type Octet is mod 2**8;
   type Double_Octet is mod 2**16;

   function Shift_Right(Value : Double_Octet; Count : Natural) return Double_Octet
     with
       Import,
       Convention => Intrinsic,
       Global     => null,
       Post       => Shift_Right'Result = Value / (2**Count);

   function High_Octet(Value : in Double_Octet) return Octet;

end Example;
