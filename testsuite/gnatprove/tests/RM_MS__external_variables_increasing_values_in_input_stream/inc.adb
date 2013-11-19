with System.Storage_Elements;

package body Inc
  with SPARK_Mode,
       Refined_State => (Sensor => S)
is
   pragma Warnings (Off);
   S : Integer
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address (16#DEADBEE0#);
   pragma Warnings (On);

   function First (Indicator : Increasing_Indicator) return Integer is
     (Indicator.First);

   function Second (Indicator : Increasing_Indicator) return Integer is
     (Indicator.Second);

   function Is_Valid (Indicator : Increasing_Indicator) return Boolean is
     (Indicator.Valid);

   function Is_Increasing (Indicator : Increasing_Indicator) return Boolean is
     (Indicator.Second > Indicator.First);

   pragma Warnings (Off);
   procedure Read (V     : out Integer;
                   Valid : out Boolean)
     with Global => S,
          Post   => (if Valid then V'Valid)
   is
      Tmp : Integer;
   begin
      pragma Warnings (On);
      Tmp := S;
      pragma Warnings (Off);
      if Tmp'Valid then
      pragma Warnings (On);
         V := Tmp;
         Valid := True;
      else
         V := 0;
         Valid := False;
      end if;
   end Read;

   procedure Increases (Result : out Increasing_Indicator)
     with Refined_Global => S
   is
   begin
      Read (Result.First, Result.Valid);
      if Result.Valid then
         Read (Result.Second, Result.Valid);
      else
         Result.Second := 0;
      end if;
   end Increases;
end Inc;
