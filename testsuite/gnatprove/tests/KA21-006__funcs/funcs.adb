package body Funcs is

   -- F simple functions

   function F2 (X : Integer) return Boolean is (X > 0);

   function F3 (X : Integer) return Boolean is (X > 0);

   function F4 (X : Integer) return Boolean;
   function F4 (X : Integer) return Boolean is (X > 0);

   function F5 (X : Integer) return Boolean is
   begin
      return X > 0;
   end F5;

   -- G functions reading global variable G

   function G2 (X : Integer) return Boolean is (G > 0);

   function G3 (X : Integer) return Boolean is (G > 0);

   function G4 (X : Integer) return Boolean;
   function G4 (X : Integer) return Boolean is (G > 0);

   function G5 (X : Integer) return Boolean is
   begin
      return G > 0;
   end G5;

   -- P functions with precondition

   function P2 (X : Integer) return Boolean is (X > 0);

   --  function P3 (X : Integer) return Boolean is (X > 0);
   --  pragma Precondition (X < 10);

   function P4 (X : Integer) return Boolean with Pre => X < 10;
   function P4 (X : Integer) return Boolean is (X > 0);

   function P5 (X : Integer) return Boolean is
   begin
      return X > 0;
   end P5;

   -- Q functions with postcondition

   function Q2 (X : Integer) return Boolean is (X > 0);

   --  function Q3 (X : Integer) return Boolean is (X > 0);
   --  pragma Postcondition (Q3'Result = (X > 0));

   function Q4 (X : Integer) return Boolean with Post => Q4'Result = (X > 0);
   function Q4 (X : Integer) return Boolean is (X > 0);

   function Q5 (X : Integer) return Boolean is
   begin
      return X > 0;
   end Q5;

   procedure Test is
      Y : Boolean;
   begin
      pragma Assert (F1 (3));
      Y := F1 (3); pragma Assert (Y = F1 (3));
      pragma Assert (F2 (3));
      Y := F2 (3); pragma Assert (Y = F2 (3));
      pragma Assert (F3 (3));
      Y := F3 (3); pragma Assert (Y = F3 (3));
      pragma Assert (F4 (3));
      Y := F4 (3); pragma Assert (Y = F4 (3));
      pragma Assert (F5 (3) = F5 (3));
      Y := F5 (3); pragma Assert (Y = F5 (3));

      G := 3;

      pragma Assert (G1 (3));
      Y := G1 (3); pragma Assert (Y = G1 (3));
      pragma Assert (G2 (3));
      Y := G2 (3); pragma Assert (Y = G2 (3));
      pragma Assert (G3 (3));
      Y := G3 (3); pragma Assert (Y = G3 (3));
      pragma Assert (G4 (3));
      Y := G4 (3); pragma Assert (Y = G4 (3));
      pragma Assert (G5 (3) = G5 (3));
      Y := G5 (3); pragma Assert (Y = G5 (3));

      --  pragma Assert (P1 (3));
      --  Y := P1 (3); pragma Assert (Y = P1 (3));
      pragma Assert (P2 (3));
      Y := P2 (3); pragma Assert (Y = P2 (3));
      --  pragma Assert (P3 (3));
      --  Y := P3 (3); pragma Assert (Y = P3 (3));
      pragma Assert (P4 (3));
      Y := P4 (3); pragma Assert (Y = P4 (3));
      pragma Assert (P5 (3) = P5 (3));
      Y := P5 (3); pragma Assert (Y = P5 (3));

      --  pragma Assert (Q1 (3) = Q1 (3));
      --  Y := Q1 (3); pragma Assert (Y = Q1 (3));
      pragma Assert (Q2 (3) = Q2 (3));
      Y := Q2 (3); pragma Assert (Y = Q2 (3));
      --  pragma Assert (Q3 (3) = Q3 (3));
      --  Y := Q3 (3); pragma Assert (Y = Q3 (3));
      pragma Assert (Q4 (3) = Q4 (3));
      Y := Q4 (3); pragma Assert (Y = Q4 (3));
      pragma Assert (Q5 (3) = Q5 (3));
      Y := Q5 (3); pragma Assert (Y = Q5 (3));
   end Test;
end Funcs;
