package body C910003_Pack is

    protected body Buffer is

       function TC_Items_Buffered (X : Boolean) return Item_Array is
         (TC_Items(1..TC_Last));

       function TC_Items_Buffered (X : Integer) return Item_Array is
         (TC_Items(1..TC_Last));

    end Buffer;

    procedure Proc is
       Item1 : constant Item_Type := PO.TC_Items_Buffered (1)     (1);
       Item2 : constant Item_Type := PO.TC_Items_Buffered (False) (2);
    begin
       null;
    end;

end C910003_Pack;
