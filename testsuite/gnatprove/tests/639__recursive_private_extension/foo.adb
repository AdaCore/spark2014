procedure Foo with SPARK_Mode is
   package A is
      type Root is tagged null record;
      type T is new Root with private;
      type A is access T'Class;
   private
      type T is new Root with record
         X : A;
      end record;
   end A;
begin
   null;
end Foo;
