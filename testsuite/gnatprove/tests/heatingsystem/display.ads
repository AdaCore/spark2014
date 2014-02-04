-- Control Panel Boundary Packages
package Display
  with Abstract_State => (Outputs with External => Async_Readers)
is
   subtype DisplayDigits is Integer range 0..9;
   subtype DigitPositions is Integer range 0..3;
   type Displays is array (DigitPositions) of DisplayDigits;

   procedure Write (Content : in Displays)
     with Global  => (Output => Outputs),
          Depends => (Outputs => Content);
   -- Put the value of the parameter Content on the Display.
   -- Content(0) is the leftmost digit.

end Display;
