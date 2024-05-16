package Random
with Abstract_State    => State,
     Initializes       => State,
     Initial_Condition => not Is_Initialised
is

   type Random_Bits is mod 2 ** 32;

   function Is_Initialised return Boolean
   with Ghost,
        Global => (Input => State);

   procedure Initialise
   with Global => (In_Out => State),
        Pre    => not Is_Initialised,
        Post   => Is_Initialised;

   procedure Get (Data : out Random_Bits)
   with Global => (In_Out => State),
        Pre    => Is_Initialised,
        Post   => Is_Initialised;

end Random;
