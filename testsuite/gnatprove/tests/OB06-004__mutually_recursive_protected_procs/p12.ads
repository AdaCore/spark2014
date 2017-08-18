package P12 is
   package P1 with
     Abstract_State => (State1 with Synchronous,
                                    External)
   is

      procedure Proxy1;

   end;

   package P2 with
     Abstract_State => (State2 with Synchronous,
                                    External)
   is

      procedure Proxy2;

   end;
end P12;
