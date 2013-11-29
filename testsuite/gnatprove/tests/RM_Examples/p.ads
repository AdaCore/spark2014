package P
  with Initializes => VP
is
   pragma Elaborate_Body;  --  Needed because VP is
   VP : Integer;           --  Initialized in the body
end P;
