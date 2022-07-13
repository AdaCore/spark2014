package A
  with Abstract_State => State,
       Initializes    => State
is
   function Return_State return Integer
     with Global   => State,
          Annotate => (GNATprove, Always_Return);
end A;
