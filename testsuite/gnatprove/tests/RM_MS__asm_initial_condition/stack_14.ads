package Stack_14
  with SPARK_Mode,
       Abstract_State    => State,
       Initializes       => State,
       Initial_Condition => Is_Empty  -- Stating that Is_Empty holds
                                      -- after initialization
is
   function Is_Empty return Boolean
     with Global => State;

   function Is_Full return Boolean
     with Global => State;

   function Top return Integer
     with Global => State,
          Pre    => not Is_Empty;

   procedure Push (X: in Integer)
     with Global => (In_Out => State),
          Pre    => not Is_Full,
          Post   => Top = X;

   procedure Pop (X: out Integer)
     with Global => (In_Out => State),
          Pre    => not Is_Empty;
end Stack_14;
