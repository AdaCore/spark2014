package body Util is
   function Extract_Unsigned_16(Query : Network_DNS_Query;
                                Offset : Network_DNS_Query_Range)
                                return Unsigned_16 is
   begin
      return Shift_Left(Unsigned_16(Query(Offset).Data), 8)
        + Unsigned_16(Query(Offset + 1).Data); -- REQ-4
   end Extract_Unsigned_16;

   function Extract_Bits_Of_Octet(Query : Network_DNS_Query;
                                  Offset : Network_DNS_Query_Range;
                                  Bit_Shift_Right : Bit_Range;
                                  Bit_Mask : Unsigned_8)
                                  return Unsigned_8 is
   begin
      return
        Shift_Right(Unsigned_8(Query(Offset).Data), Bit_Shift_Right)
        and Bit_Mask;
   end Extract_Bits_Of_Octet;

end;
