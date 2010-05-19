-- Sample random package
-- $Log: random.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/20 20:28:28  adi
-- Initial revision
--
--
package body Random is
   subtype uint32 is Long_integer range 0..2**31-1;

   function Poly1(S : Seed_range) return uint32
   is
      n : uint32;
   begin
      -- Computes 43 + 37s + 19s^2 + s^3
      n := 43 + uint32(S)*(37 + uint32(S)*(19 + uint32(S)));
      return n;
   end Poly1;

   function Poly2(s : Seed_range) return uint32
   is
      n : uint32;
   begin
      -- Computes 813 + 101s + 67s^2 + 2s^3
      n := 813 + uint32(S)*(101 + uint32(S)*(67 + 2*uint32(S)));
      return n;
   end Poly2;

   function Seed(V : Value) return Number
   is begin
      return Number'(S => Seed_range(V) mod Max_seed,
                     Last_V => V);
   end Seed;

   procedure Get(N : in out Number;
                 V : out Value)
   is
      D_S : Seed_Range;
      Tmp, P_1, P_2, P_3, P_4 : Uint32;
   begin
      D_S := Seed_Range(N.Last_V mod Max_Seed);
      P_1 := Poly1(N.S) mod Max_seed;
      P_2 := Poly1(D_s) mod Max_seed;
      P_3 := Poly2(N.S) mod Max_seed;
      P_4 := Poly2(D_s) mod Max_seed;

      tmp := (P_1 * P_2);
      N.S := Seed_Range(Tmp mod Max_seed);
      tmp := (P_3 * P_4);
      N.Last_V := Value(tmp mod Max_Val);
      V := N.Last_V;
   end Get;

end Random;
