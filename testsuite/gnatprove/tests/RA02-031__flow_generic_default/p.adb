procedure P is

   X : Integer := 0;

   generic
      F1 : Integer;
   package G1 is
   end;

   generic
      F2 : Integer := X;
   package G2 is
   end;

   package I1 is new G1 (X);  -- explicit variable in actual, NOK
   package I2 is new G2;      -- implicit variable in actual, also NOK
begin
   X := X + 1;
end;
