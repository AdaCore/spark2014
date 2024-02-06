package P with
   SPARK_Mode
is
   package Nested_1 is
      type T is private;

      function Id (X : Integer) return Integer;

      procedure P (X : Integer) with
        Import,
        Pre => X / Id (1) = X;

   private

      type T is record
         X : Positive := Id (2);
      end record;

   end Nested_1;

   package Nested_2 is
      type T is private;

      function Id (X : Integer) return Integer;

      procedure P (X : Integer) with
        Import,
        Pre => X / Id (1) = X;

   private

      type T is record
         X : Positive := Id (2);
      end record;

   end Nested_2;
end P;
