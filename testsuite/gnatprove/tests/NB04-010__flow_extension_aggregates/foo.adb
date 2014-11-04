package body Foo
is
   procedure Improve (X : Base_T;
                      Y : out Derived_T)
   is
   begin
      Y := (X with B => False);
   end Improve;
end Foo;
