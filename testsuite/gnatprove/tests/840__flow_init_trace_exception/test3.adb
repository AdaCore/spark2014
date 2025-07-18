procedure Test3 with SPARK_Mode is

   type Wrapper is record I : Integer; end record;

   function Bar (B : Boolean; X : in out Wrapper) return Boolean with
     Side_Effects, Exceptional_Cases => (Program_Error => B), Import, Global => null, Always_Terminates;

   procedure Foo is
      X : Wrapper := (I => 0);
      B : Boolean;
   begin
      B := Bar (True, X);
   exception
      when Program_Error => pragma Assert (X.I = 0);
   end Foo;
begin
   null;
end Test3;
