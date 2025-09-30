package body Array_Comparison_Nat is

   pragma Warnings (Off, "analyzing unreferenced procedure *");
   pragma Warnings (Off, "subprogram * has no effect");

   type Natural_Array is array (Integer range <>) of Natural;

   procedure P_Nat (I : Integer) is

   begin

      case I is

         --------------
         --  GROUP 1 --
         --------------

         when 11 =>
            declare
               --  "Short" array, aggregate notation, no 'others'.
               X : Natural_Array := (1 => 1, 2 .. 3 => 2, 4 => 3);
            begin
               pragma Assert (X /= X);
            end;

         when 12 =>
            declare
               --  The same array as above, aggregate notation, with 'others'.
               X : Natural_Array (1 .. 4) := (1 => 2, 4 => 3, others => 2);
            begin
               pragma Assert (X /= X);
            end;

         --------------
         --  GROUP 2 --
         --------------

         when 21 =>
            declare
               --  "Long" array aggregate, no 'others'.
               X : Natural_Array (1 .. 300) :=
                 (1          => 1,
                  2 .. 18    => 2,
                  19         => 3,
                  20         => 4,
                  21 .. 298  => 5,
                  299 .. 300 => 6);
            begin
               pragma Assert (X /= X);
            end;

         when 22 =>
            declare
               --  The same as above, with 'others'.
               X : Natural_Array (1 .. 300) :=
                 (1          => 1,
                  19         => 3,
                  20         => 4,
                  21 .. 298  => 5,
                  299 .. 300 => 6,
                  others     => 2);
            begin
               pragma Assert (X /= X);
            end;

         when others =>
            null;
      end case;
   end;

end Array_Comparison_Nat;
