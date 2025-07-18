procedure Test2 with SPARK_Mode is

   type Wrapper is record I : Integer; end record;

   procedure Bar (B : Boolean; X : in out Wrapper) with
     Exceptional_Cases => (Program_Error => B), Import, Global => null, Always_Terminates;

   procedure Foo (X : in out Wrapper);

   procedure Foo (X : in out Wrapper) is
   begin
      Bar (True, X);

   exception
      when Program_Error => null;
   end Foo;
begin
   null;
end Test2;
