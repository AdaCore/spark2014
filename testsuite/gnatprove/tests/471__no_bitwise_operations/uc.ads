with Ada.Unchecked_Conversion;

package UC is
   type Base is mod 2**32
     with Annotate => (GNATprove, No_Bitwise_Operations);

   function To_Base is new Ada.Unchecked_Conversion (Integer, Base);

end;
