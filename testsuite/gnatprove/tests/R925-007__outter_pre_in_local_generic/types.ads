package Types
is
   subtype Natural_Without_Last is Natural range 1 .. Natural'Last - 1;
   type Buffer is array (Natural_Without_Last range <>) of Integer;

end Types;
