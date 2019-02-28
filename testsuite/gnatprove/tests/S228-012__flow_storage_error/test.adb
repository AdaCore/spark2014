with Foo;

package body Test
is

   type Array_Type is array (Integer range 0 .. 10) of Integer;

   procedure Check (Success : out Boolean)
   is
      Arr : Array_Type;

      function Do_Check (T : Integer) return Boolean
      is (True);

   begin
      if (for all I of Arr => not Do_Check (I))
      then
         null;
      end if;
   end Check;

   -----------------------------------------------------------------------------

   procedure Test
   is
      Success : Boolean;
   begin
      Check (Success);
      if Success then
         Foo.Count;
      end if;
   end Test;

end Test;
