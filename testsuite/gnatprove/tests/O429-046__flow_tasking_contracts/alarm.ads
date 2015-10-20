package Alarm
  with Abstract_State =>
  (Blinkenlights with
     Synchronous, External)
is

    procedure Turn_On
    with Global => (In_Out => Blinkenlights);

    procedure Turn_Off
    with Global => (In_Out => Blinkenlights);

end Alarm;
