with TuningData;
limited with Timer, Display;

package User with
  SPARK_Mode,
  Abstract_State => (Button_State with Synchronous)
is
end User;
