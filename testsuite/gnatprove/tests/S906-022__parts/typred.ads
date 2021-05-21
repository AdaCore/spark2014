package Typred is

   type T is record
      A : Boolean;
      B : Boolean;
   end record;

   subtype S is T with Predicate => S.A and then S.B;

   procedure P (X : in out S);
end Typred;
