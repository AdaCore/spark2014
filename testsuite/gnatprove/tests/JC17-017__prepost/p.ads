package P is
   function F1 (X, Y : Integer) return Integer;
   pragma Precondition (X + Y < 0);

   function F2 (X, Y : Integer) return Integer;
   pragma Precondition (True);

   function F3 (X, Y : Integer) return Integer;
   pragma Precondition (X + Y < 0);

   function F3 (X, Y : Integer) return Integer is (X + Y);

   function F4 (X, Y : Integer) return Integer;
   pragma Precondition (True);

   function F4 (X, Y : Integer) return Integer is (X + Y);
end;
