with X.Y;

package body X
   with Refined_State =>
      (channel => X.Y.channel)
is

   procedure init
   is
   begin
      Y.init;
   end init;

end X;
