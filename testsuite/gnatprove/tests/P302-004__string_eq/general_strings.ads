with Ada.Strings.Bounded;

   package General_Strings is
     new Ada.Strings.Bounded.Generic_Bounded_Length (Max => 255);
