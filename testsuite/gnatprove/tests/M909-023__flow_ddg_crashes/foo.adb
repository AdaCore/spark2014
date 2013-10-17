package body Foo
is

   Y : Boolean;

   procedure A is
   begin
      Y := not Y;
   end A;

   procedure B is
   begin
      if Y then
         Y := False;
      end if;
   end B;

   procedure Do_Test is
   begin
      Y := False;
      loop
         A;
         B;
         --  This used to crash: we had undue control dependency
         --  introduced on the last global vertex of B; the DDG
         --  prettyfier's sanity check then rightly complained causing
         --  a bug box.
      end loop;
   end Do_Test;

end Foo;
