with X.Y.Z;

package body X.Y
   with Refined_State => (
      channel => X.Y.Z.channel)
is
   procedure init
   is
   begin
      -- Init private child
      Z.init;
   end init;

end X.Y;
