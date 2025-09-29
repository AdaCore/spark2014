package R is
   --  Identical specs, one state is null, the other is not

   package A with Abstract_State => State is
      function F return Integer with Global => State;
   end;

   package B with Abstract_State => State is
      function F return Integer with Global => State;
   end;
end;
