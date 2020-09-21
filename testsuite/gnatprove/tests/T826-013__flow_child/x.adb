with X.Y;

package body X
   with Refined_State =>
      (channel_x => X.Y.channel_y)
is

   procedure init_x
   is
   begin
      Y.init_y;
   end init_x;

end X;
