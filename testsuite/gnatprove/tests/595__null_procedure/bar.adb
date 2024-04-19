procedure Bar with SPARK_Mode is
   package P is
      type Root is abstract tagged record X : Integer; end record;
      procedure Set_Field (R : in out Root) is abstract
        with Global => null, Post'Class => R.X = 1; -- @POSTCONDITION:FAIL
      type Child is new Root with null record;
      procedure Set_Field (R : in out Child) is null;
   end P;

   Y : P.Child := (X => 42);
begin
   P.Set_Field (P.Root'Class (Y));
end Bar;
