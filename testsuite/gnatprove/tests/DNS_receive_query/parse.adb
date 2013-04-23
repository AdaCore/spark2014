with Util; use Util;

-- FIXME: GNATprove cannot prove this function?
package body Parse is
   procedure Parse_Header(Query : Network_DNS_Query;
                          Result : out Parse_Result_T) is
      Opcode : Unsigned_8;
      Qdcount : Unsigned_16;
      Count   : Unsigned_16;
      Header : Query_Header;
   begin
      Header.ID := Extract_Unsigned_16(Query, 0); -- REQ-6.1

      -- REQ-6.2
      if Extract_Bits_Of_Octet(Query => Query, Offset => 2,
                               Bit_Shift_Right => 7, Bit_Mask => 1) /= 0 then
         Result := (Return_Code => Invalid_Query);
         return;
      end if;

      -- REQ-6.3
      Opcode := Extract_Bits_Of_Octet(Query => Query, Offset => 2,
                                      Bit_Shift_Right => 3,
                                      Bit_Mask => 2#1111#);
      case Opcode is
      when 0 =>
         Header.OPCODE := Standard_Query;

      when 1 =>
         Header.OPCODE := Inverse_Query;

      when others =>
         Result := (Return_Code => Invalid_Query);
         return;
      end case;

      -- REQ-6.4 and REQ-6.4.0
      if Extract_Bits_Of_Octet(Query => Query, Offset => 2,
                               Bit_Shift_Right => 0,
                               Bit_Mask => 2#110#) /= 0
        or Query(3).Data /= 0 then
         Result := (Return_Code => Invalid_Query);
         return;
      end if;

      -- REQ-6.5
      Qdcount := Extract_Unsigned_16(Query, 4);
      if Qdcount >= Unsigned_16(Qdcount_Range'First)
        and Qdcount <= Unsigned_16(Qdcount_Range'Last) then
         Header.QDCOUNT := Qdcount_Range(Qdcount);
      else
         Result := (Return_Code => Invalid_Query);
         return;
      end if;

      -- REQ-6.6
      Count := Extract_Unsigned_16(Query, 6);
      if Count /= 0 then
         Result := (Return_Code => Invalid_Query);
         return;
      end if;

      Count := Extract_Unsigned_16(Query, 8);
      if Count /= 0 then
         Result := (Return_Code => Invalid_Query);
         return;
      end if;

      Count := Extract_Unsigned_16(Query, 10);
      if Count /= 0 then
         Result := (Return_Code => Invalid_Query);
         return;
      end if;

      Result := (Return_Code => OK, Header => Header);
      return;
   end Parse_Header;
end;
