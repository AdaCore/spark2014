pragma SPARK_Mode;
package body CC
is

   procedure Next_Day (D : Days; N : out Days)
   is
   begin
      if D in Mon .. Sat then
         N := Days'Succ (D);
      else
         N := Mon;
      end if;
   end Next_Day;

end CC;
