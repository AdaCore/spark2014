package Test is

   type Ar is array (1..10) of Integer;

   type T is record
      A : Integer;
      B : Boolean;
      C : Ar;
   end record;

   type ArT is array (10 .. 20) of T;
   type MatT is array (10 .. 20, 30 .. 40) of T;

   function F1 (X : T) return Integer
      with Pre => (X.A > 10),
           Post => (F1'Result > 10);

   function F2 (X : T) return Integer
      with Pre => (X.C (1) > 11),
           Post => (F2'Result > 11);

   function F3 (X : ArT) return Integer
      with Pre => (X (10).C (1) > 11),
           Post => (F3'Result > 11);

   procedure P1 (X : in out T)
      with Post => (X.A = 1);

   procedure P2 (X : in out T)
      with Post => (X.C (2) = 1);

   procedure P3 (X : in out ArT)
      with Post => (X (11).C (2) = 1);

--   procedure P4 (X : in out MatT)
--      with Post => (X (15, 35).C (2) = 1);
end Test;
