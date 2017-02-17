package body Test is

   function F1 (X : T) return Integer
   is
   begin
      return X.A;
   end F1;

   function F2 (X : T) return Integer
   is
   begin
      return X.C (1);
   end F2;

   function F3 (X : ArT) return Integer
   is
   begin
      return X (10).C (1);
   end F3;

   procedure P1 (X : in out T) is
   begin
      X.A := 1;
   end P1;

   procedure P2 (X : in out T) is
   begin
      X.C (2) := 1;
   end P2;

   procedure P3 (X : in out ArT) is
   begin
      X (11).C (2) := 1;
   end P3;

--   procedure P4 (X : in out MatT) is
--   begin
--      X (15, 35).C (2) := 1;
--   end P4;

end Test;
