procedure C380001 is

   type R2;

   type R3 (D : access R2) is limited null record;

   type R2 is limited record
      C : R3 (R2'Access);
   end record;

   type A is access R2;

   X : A;

begin
   X := new R2;
end C380001;
