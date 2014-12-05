with Ada.Sequential_IO;

package body Use_Seq_IO with
  SPARK_Mode => Off
is
   procedure Dummy is
   begin
      null;
   end Dummy;

   package IO is new Ada.Sequential_IO (Integer);
end Use_Seq_IO;
