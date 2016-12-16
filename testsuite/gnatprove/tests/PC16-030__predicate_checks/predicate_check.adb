procedure Predicate_Check with SPARK_Mode is
   type R is record
      F : Integer;
   end record;

   package Nested is
      subtype S is R with Predicate => S.F = 42;
      procedure P (X : in out S) is null;

      type T is private;
      procedure P (X : in out T) is null;
   private
      type T is new S;
   end Nested;

   X : Nested.T;
   Y : Nested.S;
begin
   Nested.P (X);
   Nested.P (Y);
end Predicate_Check;
