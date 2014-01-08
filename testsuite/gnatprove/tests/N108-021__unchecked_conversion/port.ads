package Port
is
   pragma Elaborate_Body;

   type U32 is mod 2**32;

   subtype S1 is Integer range 0 .. 17;

   V1Raw : U32
     with Volatile,
          Async_Writers => True;

end Port;
