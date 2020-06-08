package A with Initializes => (X, B.Y) is
   X : Integer := 0;
   package B with Initializes => Y is
      Y : Integer := 0;
   end B;
end A;
