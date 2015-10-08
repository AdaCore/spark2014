with Ticks_Per_Second;

package body Nano is

   function Id (X : Integer) return Integer is
   begin
      pragma Assert (Ticks_Per_Second in 1 .. 10);
      return (X);
   end;

end;
