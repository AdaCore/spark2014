package body Foo
is
   procedure Test_01 (O : out Boolean)
   is
   begin
      O := False;
      for I in 1 .. 10 loop
         declare
            function F return Boolean
            with Pre => True
            is
            begin
               return O xor (I mod 2 = 0);
            end F;
         begin
            O := F;
         end;
      end loop;
   end Test_01;
end Foo;
