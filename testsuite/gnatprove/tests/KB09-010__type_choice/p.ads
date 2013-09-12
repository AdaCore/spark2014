package P is
   subtype Any_Priority       is Integer      range  0 .. 31;
   subtype Priority           is Any_Priority range  0 .. 30;
   subtype Interrupt_Priority is Any_Priority range 31 .. 31;

   Default_Priority : constant Priority := 15;

   type Priorities_Mapping is array (Any_Priority) of Integer;
--   pragma Suppress_Initialization (Priorities_Mapping);

   Underlying_Priorities : constant Priorities_Mapping :=
     (Priority'First ..
      Priority'Last           => 6,
      Interrupt_Priority      => 15);

   function F (X : Any_Priority) return Integer;
end P;
