package body Array_Comparison_Nat2 is

   pragma Warnings (Off, "analyzing unreferenced procedure *");
   pragma Warnings (Off, "subprogram * has no effect");

   --  NOTE: This unit is for testing the printing of multidimensional arrays
   --  in counterexamples. However, currently the counterexamples for
   --  multidimensional arrays are not well supported by the provers and hence
   --  this test set is very minimal. To be extended in the future.

   procedure P_Nat (I : Integer) is

   begin

      case I is

         --------------
         --  GROUP 1 --
         --------------

         when 11 =>
            declare
               --  "Short" array, no 'others'.
               X : Natural_Array_2D :=
                 (1 => (1 => 11, 2 => 12, 3 => 13, 4 => 14),
                  2 => (1 => 21, 2 => 22, 3 => 23, 4 => 24));
            begin
               pragma Assert (X /= X);
            end;

         when 12 =>
            declare
               --  The same array as above, with 'others'.
               X : Natural_Array_2D (1 .. 2, 1 .. 4) :=
                 (1 => (1 => 11, 2 => 12, others => 10),
                  2 => (1 => 21, 2 => 22, others => 20));
            begin
               pragma Assert (X /= X);
            end;

         --------------
         --  GROUP 2 --
         --------------

         when 21 =>
            declare
               --  "Long" array, no 'others'.
               X : Natural_Array_2D :=
                 (1  => (1 => 11, 2 => 12, 3 => 13, 4 => 14),
                  2  => (1 => 21, 2 => 22, 3 => 23, 4 => 24),
                  3  => (1 => 999, 2 => 999, 3 => 999, 4 => 999),
                  4  => (1 => 999, 2 => 999, 3 => 999, 4 => 999),
                  5  => (1 => 999, 2 => 999, 3 => 999, 4 => 999),
                  6  => (1 => 999, 2 => 999, 3 => 999, 4 => 999),
                  7  => (1 => 999, 2 => 999, 3 => 999, 4 => 999),
                  8  => (1 => 999, 2 => 999, 3 => 999, 4 => 999),
                  9  => (1 => 999, 2 => 999, 3 => 999, 4 => 999),
                  10 => (1 => 999, 2 => 999, 3 => 999, 4 => 999));
            begin
               pragma Assert (X /= X);
            end;

         when 22 =>
            declare
               --  The same array as above, with 'others'.
               X : Natural_Array_2D (1 .. 10, 1 .. 4) :=
                 (1      => (1 => 11, 2 => 12, 3 => 13, 4 => 14),
                  2      => (1 => 21, 2 => 22, 3 => 23, 4 => 24),
                  others => (others => 999));
            begin
               pragma Assert (X /= X);
            end;

         when others =>
            null;
      end case;
   end;

end Array_Comparison_Nat2;
