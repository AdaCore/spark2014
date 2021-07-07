separate (P)
package body Inner
  with SPARK_Mode => Off
is
   procedure Do_Nothing (S : in Integer; R : out Integer) is
   begin
      null;
   end Do_Nothing;
end Inner;
