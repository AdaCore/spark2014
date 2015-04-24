package body Array_Conv is
   procedure Convert (X1 : in out A1; X2 : in out A2;
                      X3 : in out A3; X4 : in out A4;
                      X5 : in out A5; X6 : in out A6) is
   begin
      X1 := A1(X2);
      X1 := A1(X3);
      X1 := A1(X4);
      X1 := A1(X5);
      X1 := A1(X6);

      X2 := A2(X1);
      X2 := A2(X3);
      X2 := A2(X4);
      X2 := A2(X5);
      X2 := A2(X6);

      X3 := A3(X1);
      X3 := A3(X2);
      X3 := A3(X4);
      X3 := A3(X5);
      X3 := A3(X6);

      X4 := A4(X1);
      X4 := A4(X2);
      X4 := A4(X3);
      X4 := A4(X5);
      X4 := A4(X6);

      X5 := A5(X1);
      X5 := A5(X2);
      X5 := A5(X3);
      X5 := A5(X4);
      X5 := A5(X6);

      X6 := A6(X1);
      X6 := A6(X2);
      X6 := A6(X3);
      X6 := A6(X4);
      X6 := A6(X5);
   end Convert;
end Array_Conv;
