package Reproduce with SPARK_Mode is

   type T1 is tagged private;
   procedure Foo  (X : in out T1);

private

   type T2 is tagged null record;
   procedure Bar (Y : in out T2);

   type Any_T2 is access T2'Class;

   type T1 is tagged record
      Z : Any_T2;
   end record;

end Reproduce;
