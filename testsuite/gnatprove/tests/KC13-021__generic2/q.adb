package body Q is

   function QF1 (J : Integer) return Integer is
   begin
      return 0;
   end;

   procedure QP1 (J : in out Integer) is
   begin
      J := J + 1;
   end;

   package P2 is new P (4, 3, 2, 1, Boolean, Integer, Natural, QF1, QP1);

   procedure QP (X1 : Boolean; X2 : Integer; X3 : Natural; X4 : out Integer) is
      R1 : P1.R;
      R2 : P2.R;
   begin
      R1 := P1.Pack (X2, X1, X3);
      R2 := P2.Pack (X1, X2, X3);
      X4 := R1.D + R2.D;
   end;

end;
