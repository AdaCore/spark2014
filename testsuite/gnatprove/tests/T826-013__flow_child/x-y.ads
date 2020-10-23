private package X.Y
   with Abstract_State =>
      (channel with Part_Of => X.channel)
is
   procedure init; -- with Global => (output => channel);
end X.Y;
