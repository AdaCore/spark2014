procedure Test with SPARK_Mode is

   type Wrapper is record I : Integer; end record;

   procedure Bar (B : Boolean; X : in out Wrapper) with
     Exceptional_Cases => (Program_Error => B), Import, Global => null, Always_Terminates;

   procedure Foo is
      X : Wrapper := (I => 0);
   begin
      Bar (True, X);

   exception
      when Program_Error => pragma Assert (X.I = 0);
   end Foo;
begin
   null;
end Test;
