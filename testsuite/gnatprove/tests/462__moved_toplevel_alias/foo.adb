procedure Foo with SPARK_Mode is
   type R is record
      Held : aliased Integer;
   end record;
   type Arr is array (Positive range <>) of R;
   type Acc is access all Integer;
   X : Arr := (1 => (Held => 0));
begin
   declare
      Y : Acc := X(1 .. 1) (1 .. 1) (1).Held'Access;
      Z : Acc := X(1).Held'Access;
   begin
      Y.all := 1;
      pragma Assert (Y.all /= Z.all);
   end;
end Foo;
