package P is

   type Array_Type is array (Integer range <>) of Boolean;

   protected PO1 is
      entry Init_Element (A : out Boolean);
   end PO1;

   protected PO2 is
      entry Init_Elements (A : out Array_Type);
   end PO2;

   procedure Init_Array (My_Array : out Array_Type);

end P;
