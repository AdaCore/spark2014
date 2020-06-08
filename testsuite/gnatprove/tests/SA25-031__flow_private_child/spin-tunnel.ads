private package sPIN.Tunnel
with
   Abstract_State => ((Tunnel_Internal with Part_Of => Internal_State),
                      (Tunnel_External with External, Part_Of => External_State)),
   Initializes => Tunnel_Internal,
   Initial_Condition => not Is_Valid
is

   procedure Became_Valid
      (Result : out Boolean)
   with
      Pre  => not Is_Valid,
      Post => Result = Is_Valid;

   procedure Still_Valid
      (Result : out Boolean)
   with
      Pre  => Is_Valid,
      Post => Result = Is_Valid;

   function Is_Valid return Boolean
   with
      Ghost;

end sPIN.Tunnel;
