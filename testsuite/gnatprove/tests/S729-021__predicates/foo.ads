package Foo with
  SPARK_Mode
is

   type Context_Type is private;

   procedure Initialize (Context : out Context_Type) with
     Post => Valid (Context);

   function Valid (Context : Context_Type) return Boolean;

   function Valid_X (X : Natural) return Boolean is
      (X > 10);

private

   type Context_Type is
      record
         X : Natural;
      end record with
     Dynamic_Predicate => Valid_X (X);

end Foo;
