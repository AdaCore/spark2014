package body Sqrt
  with SPARK_Mode
is

  -- The function below calculates the square root of a
  -- natural number.

   function SQRT (N : Natural) return Natural
   is
      Lower, Upper, Middle : Natural;
      Maximum_Root : constant Natural := 46341; -- (Natural'Last = 2**31-1)
   begin
      Lower := 0;

      if N >= Maximum_Root then
         Upper := Maximum_Root;
      else
         Upper := N + 1;
      end if;

      loop
         pragma Loop_Invariant (0 <= Lower and
                                Lower < Upper and
                                Upper <= Maximum_Root and
                                Lower * Lower <= N and
                                N < Upper * Upper);
         exit when Lower + 1 = Upper;
         Middle := (Lower + Upper) / 2;
         if Middle * Middle > N then
            Upper := Middle;
         else
            Lower := Middle;
         end if;
      end loop;
      return Lower;
   end SQRT;

end Sqrt;
