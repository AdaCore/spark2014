pragma SPARK_Mode (On);

package body Ethernet_Dissector is

    function Convert_To_Two_Octets is new Convert_To (Two_Octets);
    function Convert_To_Four_Octets is new Convert_To (Four_Octets);
    function Convert_To_Six_Octets is new Convert_To (Six_Octets);

    function Match (Buffer : Bytes) return Natural is
        Offset : Natural := 0;
        EtherType_Length_1 : Bytes (1 .. 2);
        EtherType_Length_2 : Bytes (1 .. 2);
        EtherType_Length_3 : Bytes (1 .. 2);
        Length : Bytes (1 .. 2);
    begin
        if Buffer'First /= 1 or Buffer'Length < 60 or Buffer'Length > 1520 then
            return 0;
        end if;

        pragma Assert(Buffer'Length > 5);
        Bytes_Put (Buffer (Buffer'First .. Buffer'First + 5));

        Bytes_Put (Buffer (Buffer'First + 6 .. Buffer'First + 11));

        EtherType_Length_1 := Buffer (Buffer'First + 12 .. Buffer'First + 13);
        case Convert_To_Two_Octets (EtherType_Length_1) is
            when 16#8100# =>
                Bytes_Put (Buffer (Buffer'First + 12 .. Buffer'First + 15));
                Offset := Offset + 4;
            when 16#88A8# =>
                Bytes_Put (Buffer (Buffer'First + 12 .. Buffer'First + 15));
                Offset := Offset + 4;
                EtherType_Length_2 := Buffer (Buffer'First + 16 .. Buffer'First + 17);
                case Convert_To_Two_Octets (EtherType_Length_2) is
                    when 16#8100# =>
                        Bytes_Put (Buffer (Buffer'First + 16 .. Buffer'First + 19));
                        Offset := Offset + 4;
                    when others =>
                        return 0;
                end case;
            when others =>
                null;
        end case;

        EtherType_Length_3 := Buffer (Buffer'First + 12 + Offset .. Buffer'First + 13 + Offset);
        case Convert_To_Two_Octets (EtherType_Length_3) is
            when 0 .. 1500 =>
                Length := Buffer (Buffer'First + 12 + Offset .. Buffer'First + 13 + Offset);
                Bytes_Put (Length);
                if 15 + Offset + Natural (Convert_To_Two_Octets (Length)) - 1 /= Buffer'Length then
                    return 0;
                end if;
                Bytes_Put (Buffer (Buffer'First .. Buffer'First + Natural (Convert_To_Two_Octets (Length)) - 1));
            when 1501 .. 1535 =>
                return 0;
            when 1536 .. 65535 =>
                Bytes_Put (Buffer (Buffer'First + 12 + Offset .. Buffer'First + 13 + Offset));
                Bytes_Put (Buffer (Buffer'First .. Buffer'First + Buffer'Length - 15 - Offset));
        end case;
        return Buffer'Length;
    end Match;

end Ethernet_Dissector;
