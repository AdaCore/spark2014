procedure Foo with SPARK_Mode is

   type Half_Byte is mod 2 ** 4 with Size => 4;
   type Word is mod 2 ** 32 with Size => 32;
   type Word_Array is array (Integer range 0 .. 4) of Word;

   function Bar (Data : aliased Word_Array) return Word;

   function Bar (Data : aliased Word_Array) return Word is
      type Half_Byte_Array is
        array (Integer range 1 .. (Data'Length * 8))
          of Half_Byte
            with Pack;

      Q_Arr : constant Half_Byte_Array with Address => Data'Address, Import;
   begin
      pragma Assert (Half_Byte_Array'Size = 160);
      pragma Assert (Half_Byte_Array'Alignment = 1);
      return 0;
   end Bar;

   package Baz is
     function P (Data : aliased Word_Array) return Word;
   end Baz;

   package body Baz is
      function P (Data : aliased Word_Array) return Word is
	 type Half_Byte_Array is
	   array (Integer range 1 .. (Data'Length * 8))
	   of Half_Byte
	   with Pack;

	 Q_Arr : constant Half_Byte_Array with Address => Data'Address, Import;
      begin
	 pragma Assert (Half_Byte_Array'Size = 160);
	 pragma Assert (Half_Byte_Array'Alignment = 1);
	 return 0;
      end P;
   end Baz;
begin
   null;
end Foo;
