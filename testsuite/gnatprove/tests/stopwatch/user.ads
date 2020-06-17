with TuningData;
with Timer;
with Display;

package User with
  SPARK_Mode
is

   protected Buttons is
      pragma Interrupt_Priority (TuningData.UserPriority);

      procedure StartClock with
        Global => (In_Out => Timer.Control),
        Attach_Handler => 1;
      pragma Annotate (GNATprove, False_Positive,
                       "this interrupt might be reserved",
                       "The interrupt is not reserved.");

      procedure StopClock with
        Global => (In_Out => Timer.Control),
        Attach_Handler => 2;
      pragma Annotate (GNATprove, False_Positive,
                       "this interrupt might be reserved",
                       "The interrupt is not reserved.");

      procedure ResetClock with
        Global => (Output => Display.LCD),
        Attach_Handler => 3;
      pragma Annotate (GNATprove, False_Positive,
                       "this interrupt might be reserved",
                       "The interrupt is not reserved.");
   end Buttons;

end User;
