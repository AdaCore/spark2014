pragma SPARK_Mode (On);

package body Count is

   procedure resetCounter (counter : out Integer) is
   begin
      counter := 0;
   end resetCounter;

   procedure addOne (counter: in out Integer) is
   begin
      counter := counter + 1;
   end addOne;

end Count;
