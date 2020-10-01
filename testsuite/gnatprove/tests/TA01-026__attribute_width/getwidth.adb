procedure Getwidth is
   generic
      type E is (<>);
   procedure P;

   function IDENT_INT (X : Integer) return Integer is (X);

   procedure P is
      SUBTYPE NOENUM IS E RANGE
        E'VAL (IDENT_INT(2)) .. E'VAL (IDENT_INT(1));

      X : Integer := NOENUM'Width;
   begin
      pragma Assert (X > 0);
   end P;

   type E is (A, B, C);
   procedure Proc1 is new P(E);
begin
   Proc1;
end Getwidth;
