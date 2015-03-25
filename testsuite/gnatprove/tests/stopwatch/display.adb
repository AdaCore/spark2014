with System.Storage_Elements;

package body Display with
  SPARK_Mode,
  Refined_State =>
    (Port_State => Port,
     State      => Internal_State)
is
   Internal_State : PT;
   Port : Integer with
     Volatile,
     Async_Readers,
     Effective_Writes,
     Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#);

   protected body PT is
      procedure Increment with
        Refined_Global  => (Output => Port),
        Refined_Depends => ((Port, PT) => PT)
      is
      begin
         Counter := Counter + 1;
         Port := Counter;
      end Increment;

      procedure Reset with
        Refined_Global  => (Output => Port),
        Refined_Depends => ((Port, PT) => null)
      is
      begin
         Counter := 0;
         Port := Counter;
      end Reset;
   end PT;

   procedure Initialize
   is
   begin
      Internal_State.Reset;
   end Initialize;

   procedure AddSecond
   is
   begin
      Internal_State.Increment;
   end AddSecond;

end Display;
