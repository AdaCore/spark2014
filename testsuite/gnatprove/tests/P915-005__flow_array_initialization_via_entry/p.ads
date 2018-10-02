package P is

   type Array_Type is array (Integer range <>) of Boolean;

   protected PO is
      entry Init_Element (A : out Boolean);
   end PO;

   procedure Init_Array (My_Array : out Array_Type);

end P;
