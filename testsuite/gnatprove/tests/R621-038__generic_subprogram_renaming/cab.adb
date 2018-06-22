with exchange;

procedure cab (a, b, c : in out thing) is

   procedure swap is new exchange (item => thing);

begin

   swap (a, b);

   swap (a, c);

end cab;
