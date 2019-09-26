with Types;
procedure Main with SPARK_Mode
is

    subtype Packet is Types.Bytes (1 .. 1500);
    Buffer : Types.Bytes_Ptr := new Packet'(others => 0);

begin
    pragma Assert (False);
end Main;
