package Buf_Read is

   function Valid (C : Character) return Boolean;

   function Valid_State return Boolean;

   procedure Next_Char (C : out Character)
      with Pre  => (Valid_State),
           Post => (Valid (C) and then Valid_State);

end Buf_Read;
