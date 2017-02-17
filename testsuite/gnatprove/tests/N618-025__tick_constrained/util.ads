with Types; use Types;
with Interfaces; use Interfaces;

package Util is pragma SPARK_Mode (On);
   function Extract_Unsigned_16(Query : Network_DNS_Query;
                                Offset : Network_DNS_Query_Range)
                                return Unsigned_16
   with
     Pre => Offset <= Network_DNS_Query_Range'Last - 1; -- at least two octets

   function Extract_Bits_Of_Octet(Query : Network_DNS_Query;
                                  Offset : Network_DNS_Query_Range;
                                  Bit_Shift_Right : Bit_Range;
                                  Bit_Mask : Unsigned_8)
                                  return Unsigned_8;
end;
