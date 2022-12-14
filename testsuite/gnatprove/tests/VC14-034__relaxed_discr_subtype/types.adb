package body Types with SPARK_Mode is

   procedure Write_Part (X : out T; C : Boolean) is
      subtype S is T (True); --  Useless, just to make the discrepency occur
   begin
      if C then
         if X.B then
            X.X := 0;
         else
            X.Y := 0;  --  V.Y might not be initialized, but nobody complains
                       --  because S makes it so that T is seen as containing
                       --  only relaxed parts.
         end if;
      end if;
   end Write_Part;

end Types;
