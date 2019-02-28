with Failed;

procedure C57004A is
begin

   LOOP4 :
   for A in 1 .. 1 loop

      for I in INTEGER range 1 .. 10 loop
         case A is
            when 1 =>
               exit LOOP4;
               Failed ("EXIT NOT OBEYED " & "(4)"); -- genuinely unreachable
         end case;
         Failed ("EXIT NOT OBEYED (4BIS)");         -- genuinely unreachable
      end loop;

   end loop LOOP4;

end C57004A;
