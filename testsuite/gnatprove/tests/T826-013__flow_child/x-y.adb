with X.Y.Z;

package body X.Y
   with Refined_State => (
      channel_y => X.Y.Z.channel_z)
is
   procedure init_y
   is
   begin
      -- Init private child
      Z.init_z;
   end init_y;

end X.Y;
