-- Control Panel Boundary Packages

package Display
--# own out Outputs : Displays;
is pragma SPARK_Mode (On);
   subtype DisplayDigits is Integer range 0..9;
   subtype DigitPositions is Integer range 0..3;
   type Displays is array (DigitPositions) of DisplayDigits;

   function PF_Write return Displays;

   procedure Write (Content : in Displays)
     with Post => (PF_Write = Content);
   --# global  out Outputs;
   --# derives Outputs from Content;
   --# post Outputs = Content;
   --
   -- Put the value of the parameter Content on the Display.
   -- Content(0) is the leftmost digit.

end Display;
