procedure Test with SPARK_Mode is

   function Rand (X : Integer) return Boolean with
     Global => null,
     Import;

   package Nested is
      type P is private;

      type Root is tagged record
         F : Integer := 1;
      end record;

      type Child is new Root with record
         G : Integer;
      end record with Predicate => Rand (2);

   private
      pragma SPARK_Mode (Off);
      type P is record
         F : Integer := 1;
      end record;
   end Nested;

   type R is record
      X : Nested.P;
   end record with
     Predicate => Rand (1);

   X : R; --  @PREDICATE_CHECK_ON_DEFAULT_VALUE:FAIL
   Y : Nested.Child; --  @PREDICATE_CHECK_ON_DEFAULT_VALUE:FAIL
begin
   null;
end;
