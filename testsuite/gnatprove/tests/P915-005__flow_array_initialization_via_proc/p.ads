package P is

   type Array_Type is array (Integer range <>) of Boolean;

   procedure Init_Element (A : out Boolean);
   procedure Init_Array (My_Array : out Array_Type);

end P;
