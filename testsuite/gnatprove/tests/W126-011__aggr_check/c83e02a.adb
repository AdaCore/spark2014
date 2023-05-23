procedure C83E02A is

   type T is record
      Value : Integer range 1 .. 3;
   end record;

   procedure P (B : Integer) is
      X : T;
   begin
      X := (Value => B);
   end P;

begin
   P (3);
end C83E02A;
