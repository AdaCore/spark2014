with Foo;

package body Usefoo
is

   procedure Do_Something (B : in out Types.Buffer;
                           R : out Integer)
   is
      package F is new Foo (B (B'First .. B'First + B'Length / 2 - 1));
   begin
      R := F.Get (B'First + B'Length / 2 - 1);
      B (B'First) := 0;
   end Do_Something;

end Usefoo;
