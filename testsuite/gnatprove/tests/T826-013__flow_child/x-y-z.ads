private package X.Y.Z
   with Abstract_State => (
      (channel_z with
         Part_Of => X.Y.channel_y))
is
   procedure init_z
      with Global  => (Output => channel_z),
           Depends => (channel_z => null);
end X.Y.Z;
