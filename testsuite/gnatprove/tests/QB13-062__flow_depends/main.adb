with Read;

package body Main with Refined_State => (S => (C1, C2)) is

   C1 : Integer := 0;
   C2 : Integer := 0;
   --  Dummy constituents; only to provide a non-trivial refinement

   procedure Test is
   begin
      pragma Assert (Read);
   end;

end;
