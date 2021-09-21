package P with Initializes => X is
   X : Integer := 0 with Alignment => 4;
   Y : Integer := 1 with Address => X'Address, Alignment => 4;
end;
