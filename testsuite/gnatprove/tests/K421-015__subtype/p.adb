procedure P is
   procedure Proc (W, X, Y, Z : Integer) is
      subtype S1 is Integer range W .. X;
      subtype S2 is S1 range Y .. Z;
   begin
      null;
   end;
   One : constant Integer := 1;
begin
   Proc (1, 4, 2, 3);  --  ok
   Proc (1, 4, 3, 2);  --  ok S2 empty
   Proc (2, 3, 4, 1);  --  ok S2 empty
   Proc (4, 1, 3, 2);  --  ok S1 and S2 empty
   Proc (3, 2, 4, 1);  --  ok S1 and S2 empty
   Proc (One, One + 1, One + 2, One + 3);
end;
