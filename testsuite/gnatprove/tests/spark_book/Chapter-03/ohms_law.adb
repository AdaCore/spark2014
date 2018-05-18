with Common_Units; use type Common_Units.Ohms;
with Ada.Text_IO;  use Ada.Text_IO;
procedure Ohms_Law is

   package Ohm_IO  is new Fixed_IO (Common_Units.Ohms);
   package Amp_IO  is new Fixed_IO (Common_Units.Amps);
   package Volt_IO is new Fixed_IO (Common_Units.Volts);

   A  : Common_Units.Amps;
   R1 : Common_Units.Ohms;
   R2 : Common_Units.Ohms;
   V  : Common_Units.Volts;
begin
   Put_Line ("Enter current and two resistances");
   Amp_IO.Get (A);
   Ohm_IO.Get (R1);
   Ohm_IO.Get (R2);
   V := A * (R1 + R2);
   Put ("The voltage drop over the two resistors is ");
   Volt_IO.Put (Item => V,
                Fore => 1,
                Aft  => 2,
                Exp  => 0);
   Put_Line (" volts");
end Ohms_Law;
