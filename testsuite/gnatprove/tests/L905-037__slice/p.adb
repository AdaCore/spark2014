procedure P is

    procedure Q (Y : in out String) with
      Pre  => Y'First = 2 and then Y'Last = 5,
      Post => Y'First = 2 and then Y'Last = 5;

    procedure Q (Y : in out String) is
    begin
       pragma Assert (Y'First = 2);
       pragma Assert (Y'Last = 5);
    end Q;

    X : String (1 .. 10) := (others => ' ');
    Y : String := X (2..5);

begin
    pragma Assert (Y'First = 2);
    pragma Assert (Y'Last = 5);
    Q (Y);
    Q (X (2..5));
end P;
