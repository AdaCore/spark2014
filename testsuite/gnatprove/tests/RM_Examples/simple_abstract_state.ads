package Simple_Abstract_State
  with Abstract_State => State         -- Declaration of abstract state named State
                                       -- representing internal state of the package.
is
   function Is_Ready return Boolean    -- Function checking some property of the State.
     with Global => State;             -- State may be used in a Global aspect.

   procedure Init                      -- Procedure to initialize the internal state of the package.
     with Global => (Output => State), -- State may be used in a Global aspect.
          Post   => Is_Ready;

   procedure Op (V : Integer)          -- Another procedure providing some operation on State
     with Global => (In_Out => State),
          Pre    => Is_Ready,
          Post   => Is_Ready;

end Simple_Abstract_State;
