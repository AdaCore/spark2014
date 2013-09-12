with Ada.Text_IO; use Ada.Text_IO;

package Pack is pragma SPARK_Mode (On);

   Col_Count : Positive_Count;

   procedure Inc (C : Positive_Count);

end Pack;
