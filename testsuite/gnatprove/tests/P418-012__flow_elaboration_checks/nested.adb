with Nested.Priv;

package body Nested with
   Refined_State => (State => Priv.Y)
is

   procedure Dummy is null;

   package body P is
   begin
      X := X + 1;
   end P;

end Nested;
