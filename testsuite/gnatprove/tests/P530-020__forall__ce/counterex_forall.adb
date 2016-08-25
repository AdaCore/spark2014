package body Counterex_forall
is

   --  Some examples adapted from riposte__arrays
   function Single_Char_Set_Broken (C : in Integer) return Int_Set
   is
      R : Int_Set;
   begin
      for X in 1 .. 100 loop
         R (X) := X = C;
         pragma Loop_Invariant (for all I in Integer range
                                  1..X => R (I) = (I = C + 1));
      end loop;
      return R;
   end Single_Char_Set_Broken;

   procedure Test_Invariant (R : out Int_Int) is
   begin
      for X in 1 .. 100 loop
         for Y in 1 .. 200 loop
            R (X) := R (X) + Y;
            pragma Loop_Invariant (for all I in 1 .. Y =>
                                     (for all J in 1 .. 100 =>
                                        I + J < X + Y + 1));
         end loop;
      end loop;
   end;

end Counterex_forall;
