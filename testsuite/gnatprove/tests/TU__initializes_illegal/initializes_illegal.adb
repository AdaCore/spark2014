package body Initializes_Illegal is
   package body Incorrect_Placement
     with Initializes => S
   is
      procedure Does_Nothing is begin null; end Does_Nothing;
   end Incorrect_Placement;
end Initializes_Illegal;
