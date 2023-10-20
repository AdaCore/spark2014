with P; use P;

procedure Bad_Call with SPARK_Mode is
   X0 : Integer;
   X1 : Integer := F1 (X0);
   X2 : Integer := F2 (X1) + F3 (1);
   X3 : Integer := (if F4 (1) > 0 then (case F5 (F5 (1)) is when 0 => F6 (1), when others => 0) else 0);
   X4, X5, X6 : Integer;

   Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11 : Integer;
begin
   X4 := Natural'(F7 (1));
   X5 := F8 (1) + 1;
   X6 := (if F9 (1) > 0 then F10 (1) else F11 (2));

   Y1 := F1 (Y0);
   Y2 := F2 (Y1);
   Y3 := F3 (1);
   Y4 := F4 (1);
   Y5 := F5 (1);
   Y6 := F6 (1);
   Y7 := F7 (1);
   Y8 := F8 (1);
   Y9 := F9 (1);
   Y10 := F10 (1);
   Y11 := F11 (1);

end Bad_Call;
