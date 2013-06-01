package body Test
is
   procedure Logic (A, B : Boolean)
   is
   begin
      pragma Assert (not (A or B) = ((not A) and (not B)));

      pragma Assert (not (A and B) = (not A) or (not B));

      pragma Assert ((A xor B) = ((A or B) and (not (A and B))));

      pragma Assert ((A xor B) = ((A and not B) or (not A and B)));
   end Logic;
end Test;
