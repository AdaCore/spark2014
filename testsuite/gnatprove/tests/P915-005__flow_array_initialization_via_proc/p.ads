package P is
   type My_Integer is new Integer range 1 .. 10;
   type Array_Type is array (Integer) of Boolean;

   procedure Init_Element (A : out Boolean);
   procedure Init_Array (My_Array : out Array_Type);

end P;
