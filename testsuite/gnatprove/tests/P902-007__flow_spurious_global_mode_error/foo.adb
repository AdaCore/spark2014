with Foo.Bar;

package body Foo with
   Refined_State => (State => Bar.State)
is

   procedure Test (S : String)
   is
   begin
      for I in S'Range loop
         Bar.Write (S (I) = ' ');
      end loop;
   end Test;

end Foo;
