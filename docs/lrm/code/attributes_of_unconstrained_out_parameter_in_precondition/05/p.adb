package body P is

   procedure Init (X : out A) is
   begin
      --# accept F,  23, X,    "OK" &
      --#        F, 602, X, X, "OK";
      for I in Positive range X'Range loop
         X (I) := 0;
         --# assert for all J in Positive range X'First .. I => (X (J) = 0);
      end loop;
   end Init;

end P;
