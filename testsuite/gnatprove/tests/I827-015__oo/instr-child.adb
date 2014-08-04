with Gnat.Io; use Gnat.Io;
package body Instr.Child is

   procedure Display_Value (X : Accurate_Clock) is
   begin
      Clock (X).Display_Value;
      Put (":");
      Put (Character'Val (Character'Pos ('0') + (X.MilliSec / 100) mod 10));
      Put (Character'Val (Character'Pos ('0') + (X.MilliSec / 10) mod 10));
      Put (Character'Val (Character'Pos ('0') + X.MilliSec mod 10));
   end Display_Value;

   procedure Increment (X : in out Accurate_Clock; Inc : Integer := 1) is
   begin
     Clock (X).Increment ((X.MilliSec + Inc) / 1000);
     X.MilliSec := (X.MilliSec + Inc) mod 1000;
   end Increment;

end;
