package body Loop_Tutorial
is

  -- The function below calculates the integer square root of a
  -- natural number.

  -- 1. Add a suitable loop variant and prove that the loop terminates.

  function ISQRT (N: in Natural) return Natural
     with Post => ISQRT'Result * ISQRT'Result <= N and
                    (ISQRT'Result + 1) * (ISQRT'Result + 1) > N
  is
    Lower, Upper, Middle: Natural;
    Maximum_Root: constant Natural := 46341; -- assumes Natural'Last = 2**31-1.
  begin
     Lower := 0;

     if N >= Maximum_Root then
        Upper := Maximum_Root;
     else
        Upper := N + 1;
     end if;

     loop
         --  Add a pragma Loop_Invariant and a pragma Loop_Variant here.

         pragma Loop_Invariant (Lower >= 0
                                and Upper <= Maximum_Root
                                and Lower < Upper
                                and Upper * Upper > N
                                and Lower * Lower <= N );

         pragma Loop_Variant (Increases => Lower,
--                              Decreases => Upper - Lower);  --  POST proves
                              Decreases => Upper);  --  POST does NOT prove

        exit when Lower + 1 = Upper;
        Middle := (Lower + Upper) / 2;
        if Middle * Middle > N then
           Upper := Middle;
        else
           Lower := Middle;
        end if;
     end loop;
     return Lower;
  end ISQRT;

end Loop_Tutorial;
