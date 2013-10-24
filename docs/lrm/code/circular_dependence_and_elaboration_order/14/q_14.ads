package Q_14
  with Abstract_State => Q_State,
       Initializes    => Q_State
is
   procedure Init (S : out Integer);
end Q_14;
