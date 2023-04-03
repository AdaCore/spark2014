procedure Main with SPARK_Mode, Annotate => (GNATprove, Always_Return) is
   package Par is
      type T is tagged null record;
      function Init return T is (null record);
      procedure Foo (X : T);
   end Par;

   package body Par is
      procedure Foo (X : T) is null;
   end Par;

   use Par;

   package Child is
      type U is new T with null record;
      function Init return U is (null record);
      procedure Foo (X : U);
   end Child;

   package body Child is
      procedure Foo (X : U) is
      begin
         while True loop
            null;
         end loop;
      end Foo;
   end Child;

   use Child;

   procedure Bar with Global => null is
      X_0 : U := Init;
      X : T'Class := X_0;
   begin
      Foo (X);
   end Bar;

begin
   Bar;
end Main;
