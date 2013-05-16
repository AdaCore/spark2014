package Indicator
--# own out Outputs : Settings;
is
   --# type Settings is abstract;
   --# function IsOn (S : Settings) return Boolean;

   procedure TurnOn;
   --# global  out Outputs;
   --# derives Outputs from ;
   --# post IsOn (Outputs);
   --
   -- Turns the indicator on.

   procedure TurnOff;
   --# global  out Outputs;
   --# derives Outputs from ;
   --# post not IsOn (Outputs);
   --
   -- Turns the indicator off.

end Indicator;
