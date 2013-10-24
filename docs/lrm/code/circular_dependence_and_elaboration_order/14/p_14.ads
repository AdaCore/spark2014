package P_14
  with Abstract_State => P_State,
       Initializes    => P_State
is
   procedure Init (S : out Integer);
end P_14;
