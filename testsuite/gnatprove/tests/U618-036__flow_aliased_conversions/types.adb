package body Types is
   procedure Foo (Self : in out Root_T) is
   begin
      Self.Field := Sub (Self, Constructor (3));
   end Foo;

   Overriding Procedure Foo (Self : in out Derived_T) is
   begin
      Self.Field := Sub (Self, Constructor (Self.A));
   end Foo;
end Types;
