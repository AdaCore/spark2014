package Debuglog.Client
with
   Abstract_State => State,
   Initializes    => State
is

   procedure Put (Item : Character)
   with
      Global  => (In_Out => State),
      Depends => (State =>+ Item);

   procedure Put (Item : String)
   with
      Global  => (In_Out => State),
      Depends => (State =>+ Item);

end Debuglog.Client;
