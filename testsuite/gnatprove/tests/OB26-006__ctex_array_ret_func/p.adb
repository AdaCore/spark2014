package body P is

    type Int_Array is array (Positive range <>) of Integer;

    TC_Items : Int_Array (1 .. 10) := (others => 1);
    TC_Last  : Natural := 0;

    procedure Proc is
       Int1 : constant Integer := TC_Items(1..TC_Last) (1);
    begin
       null;
    end;

end P;
