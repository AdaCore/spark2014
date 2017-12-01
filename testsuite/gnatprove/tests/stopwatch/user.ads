with TuningData;
limited with Timer, Display;

package User with
  SPARK_Mode,
  Abstract_State => (Button_State with External, Synchronous)
is
   pragma Elaborate_Body;
end User;
