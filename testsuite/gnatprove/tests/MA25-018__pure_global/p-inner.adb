separate (P)
package body Inner
  with SPARK_Mode => Off
is

   procedure Wibble (S : in Integer; R : out Integer)
   is
   begin
      R := S + 1;
   end Wibble;

end Inner;
