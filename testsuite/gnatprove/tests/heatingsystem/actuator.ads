package Actuator
--# own out Outputs : Settings;
is pragma SPARK_Mode (On);
   -- We don't know anything about how type Settings is implemented but we do need a type
   -- declaration for it so that we can declarae proof functions that use it.  The following
   -- proof type declaration does what we need.
   --# type Settings is abstract;

   -- and allows us to define this proof function
   function IsOn return Boolean;

   procedure TurnOn
     with Post => (IsOn);
   --# global  out Outputs;
   --# derives Outputs from ;
   --# post IsOn (Outputs);
   --
   -- Turns the heating on.

   procedure TurnOff
     with Post => (not IsOn);
   --# global  out Outputs;
   --# derives Outputs from ;
   --# post not IsOn (Outputs);
   --
   -- Turns the heating off.
end Actuator;
