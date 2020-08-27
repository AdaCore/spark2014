private package X.Y.Z
   with Abstract_State => (
      (channel with
         Part_Of => X.Y.channel))
is
   procedure init
      with Global  => (Output => channel),
           Depends => (channel => null);
end X.Y.Z;
