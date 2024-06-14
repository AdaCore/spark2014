package body Bar is

   function Baz (Data : aliased Word_Array) return Word is
      type Half_Byte_Array is
        array (Integer range 1 .. (Data'Length * 8))
          of Half_Byte
            with Pack;

      Q_Arr : constant Half_Byte_Array with Address => Data'Address, Import;
   begin
      pragma Assert (Half_Byte_Array'Size = 160);
      pragma Assert (Half_Byte_Array'Alignment = 1);
      return 0;
   end Baz;
end Bar;
