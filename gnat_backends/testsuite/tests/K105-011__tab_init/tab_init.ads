package  Tab_Init
is
    subtype Index is Integer range 1 .. 10;
    type Tab is array (Index) of Integer;
    Procedure Init (T : out Tab; A : in Integer);
end  Tab_Init;
