
package body Lp with
   SPARK_Mode
is

   -----------
   -- Power --
   -----------

   function Power (I : Natural) return Natural is
      type N_Array is array (Integer range <>) of Natural;
      Powers : constant N_Array := (62, 60, 58, 56, 54,
                                    52, 50, 48, 46, 44, 42,
                                    40, 38, 36, 34, 32, 30,
                                    28, 26, 24, 22, 20, 18,
                                    16, 14, 12);
      Previous : Natural := 64;
   begin
      for P of Powers loop
         exit when U64 (I) > U64'(2 ** P);
         Previous := P;
      end loop;
      return Previous;
   end Power;

   function Power1 (I : Natural) return Natural is
      type N_Array is array (Integer range <>) of Natural;
      Powers : constant N_Array := (62, 60, 58, 56, 54,
                                    52, 50, 48, 46, 44, 42,
                                    40, 38, 36, 34, 32, 30,
                                    28, 26, 24, 22, 20, 18,
                                    16, 14, 12);
      Previous : Natural := 64;
   begin
      pragma Assert (for all K of Powers => 2 ** K in U64'Range);
      for P of Powers loop
         pragma Loop_Invariant (for all K of Powers => 2 ** K in U64'Range);
         pragma Loop_Invariant (2 ** P in U64'Range);
         exit when U64 (I) > U64 (2 ** P);
         Previous := P;
      end loop;
      return Previous;
   end Power1;

   function Power2 (I : Natural) return Natural is
      type N_Array is array (Integer range <>) of Natural;
      Powers : constant N_Array := (62, 60, 58, 56, 54,
                                    52, 50, 48, 46, 44, 42,
                                    40, 38, 36, 34, 32, 30,
                                    28, 26, 24, 22, 20, 18,
                                    16, 14, 12);
      Previous : Natural := 64;
   begin
      pragma Assert (for all K of Powers => U64(2 ** K) in U64'Range);
      for P of Powers loop
         pragma Loop_Invariant (for all K of Powers => U64(2 ** K) in U64'Range);
         pragma Loop_Invariant (U64(2 ** P) in U64'Range);
         exit when U64 (I) > U64 (2 ** P);
         Previous := P;
      end loop;
      return Previous;
   end Power2;

end Lp;
