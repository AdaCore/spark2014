package body Foo
is

   Default_Width : constant Integer := 0;
   Default_Base  : constant Integer := 0;

   procedure Put (Width : Integer := Default_Width;
                  Base  : Integer := Default_Base)
   is
   begin
      null;
   end;

   procedure Foo
   is
   begin
      Put;
   end Foo;

end Foo;
