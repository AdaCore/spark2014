pragma Ada_2012;
package body Rchk
with
SPARK_Mode
is

   ----------
   -- Test --
   ----------

   procedure Test
     (Buf : Buffer;
      Size : U32)
   is
    begin
        if Buf'First < Buf'Last then
            pragma Assert (Buf'Last < U32'Last); --@ASSERT:FAIL
            if Buf'Length <= Size then
                null;
            end if;
        end if;
   end Test;

end Rchk;
