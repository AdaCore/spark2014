package body Pack is

    function Address_To_Hex (Adder: System.Address) return String is
       S : String (1..64) := (others => '0');
    begin
       Address_Value_IO.Put (S,
                             System.Storage_Elements.To_Integer (Adder),
                             Base => 16);
       return S;
    end Address_To_Hex;

end Pack;
