pragma SPARK_Mode (On);

with Types; use Types;
pragma Elaborate_All (Types);

package Ethernet_Dissector is

    type Two_Octets is mod 2**16;
    type Four_Octets is mod 2**32;
    type Six_Octets is mod 2**48;

    function Match (Buffer : Bytes) return Natural with
        Post => Match'Result = Buffer'Length or Match'Result = 0;

end Ethernet_Dissector;
