package Funcs is
   function F1 (X : Integer) return Boolean is (X > 0);
   function F2 (X : Integer) return Boolean;
   function F5 (X : Integer) return Boolean;

   G : Integer;

   function G1 (X : Integer) return Boolean is (G > 0);
   function G2 (X : Integer) return Boolean;
   function G5 (X : Integer) return Boolean;

   --  function P1 (X : Integer) return Boolean is (X > 0);
   --  pragma Precondition (X < 10);
   function P2 (X : Integer) return Boolean with Pre => X < 10;
   function P5 (X : Integer) return Boolean with Pre => X < 10;

   --  function Q1 (X : Integer) return Boolean is (X > 0);
   --  pragma Postcondition (Q1'Result = (X > 0));
   function Q2 (X : Integer) return Boolean with Post => Q2'Result = (X > 0);
   function Q5 (X : Integer) return Boolean with Post => Q5'Result = (X > 0);

end Funcs;
