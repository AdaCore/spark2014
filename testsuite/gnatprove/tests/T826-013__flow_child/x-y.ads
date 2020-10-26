private package X.Y
   with Abstract_State =>
      (channel_y with Part_Of => X.channel_x)
is
   procedure init_y; -- with Global => (output => channel);
end X.Y;
