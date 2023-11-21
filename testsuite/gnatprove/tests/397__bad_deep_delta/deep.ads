package Deep is

   type Int_Acc is access Positive;

   type A1 is array (1 .. 5) of Int_Acc;

   type R1 is record
      F, G : Int_Acc;
      L, M : A1;
   end record;

   type A2 is array (1 .. 2) of R1;

   type R2 is record
      A, B : R1;
      C, D : A2;
      E : Integer;
   end record;

   procedure Test1 (X : in out A1) with
     Pre => (for all J in X'Range => X(J) = null),
     Post => X(1).all = 2;

   procedure Test2 (X : in out R2);

end Deep;
