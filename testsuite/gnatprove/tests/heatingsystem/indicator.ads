package Indicator
--# own out Outputs : Settings;
is pragma SPARK_Mode (On);
   --# type Settings is abstract;
   function IsOn return Boolean;

   procedure TurnOn
     with Post => (IsOn);
   --# global  out Outputs;
   --# derives Outputs from ;
   --# post IsOn (Outputs);
   --
   -- Turns the indicator on.

   procedure TurnOff
     with Post => (not IsOn);
   --# global  out Outputs;
   --# derives Outputs from ;
   --# post not IsOn (Outputs);
   --
   -- Turns the indicator off.

end Indicator;
