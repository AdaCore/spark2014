package C910003_Pack is

    type Item_Type is range 1 .. 100; -- In a real application, this probably
                                      -- would be a record type.

    type Item_Array is array (Positive range <>) of Item_Type;

    protected type Buffer is
       function TC_Items_Buffered (X : Integer) return Item_Array;
       function TC_Items_Buffered (X : Boolean) return Item_Array;
    private
       Saved_Item : Item_Type := 1;
       Empty : Boolean := True;
       TC_Items : Item_Array (1 .. 10) := (others => 1);
       TC_Last  : Natural := 0;
    end Buffer;

    PO : Buffer;

    procedure Proc;

end C910003_Pack;
