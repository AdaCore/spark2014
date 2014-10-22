package C
  with Abstract_State => State,
       Initializes   => State
is
   function Return_State return Integer
     with Global => State;
end C;
