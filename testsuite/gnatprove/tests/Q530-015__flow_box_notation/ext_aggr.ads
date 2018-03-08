package Ext_Aggr is
   type My_Type is new Integer range 0 .. 10;

   type Base is tagged record
      O : My_Type;
   end record;

   type Derived is new Base with record
      B : My_Type;
   end record;

   procedure Reset (This : out Derived);

end Ext_Aggr;
