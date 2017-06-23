with Ada.Unchecked_Deallocation;

package body Test
  with SPARK_Mode => Off
is
   type Integer_Ptr is access Integer;

   procedure Dispose is new Ada.Unchecked_Deallocation
      (Integer, Integer_Ptr);

   procedure Open is
      Dir : Integer_Ptr := null;
   begin
      Dispose (Dir);
   end Open;

end Test;
