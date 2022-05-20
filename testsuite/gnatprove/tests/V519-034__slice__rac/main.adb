with Ada.Text_IO; use Ada.Text_IO;

procedure Main with SPARK_Mode is

   subtype Int     is Integer range 1 .. 20;
   subtype Sub_Int is Integer range 5 .. 7;

   type Power_Of_Two is
      (One, Two, Four, Eight, Sixteen, Thirty_Two, Sixty_Four);
   for Power_Of_Two use (One        => 1,
                         Two        => 2,
                         Four       => 4,
                         Eight      => 8,
                         Sixteen    => 16,
                         Thirty_Two => 32,
                         Sixty_Four => 64);

   type Arr1 is array (Int range <>) of Int;
   type Arr2 is array (Power_Of_Two range <>) of Int;

   function Same (A : Arr1) return Arr1 is (A);

   function Is_Equal (A : Arr1; E1, E2, E3 : Int) return Boolean is
      (A (A'First) = E1
      and then A (A'First + 1) = E2
      and then A (A'First + 2) = E3);

   function Is_Equal (A : Arr2; E1, E2, E3 , E4, E5, E6 : Int) return Boolean
   is
      (A (One) = E1
      and then A (Two) = E2
      and then A (Four) = E3
      and then A (Eight) = E4
      and then A (Sixteen) = E5
      and then A (Thirty_Two) = E6);

   function Is_Empty (A : Arr1) return Boolean is (A'First > A'Last);

   --  Local variables

   Twenty   : constant Arr1 (Int) := (for I in Int => I);
   Six_Four : constant Arr2 (Power_Of_Two) := (others => 6);

   Low  : constant Int := 12;
   High : constant Int := 14;

   A1 : Arr1 (4 .. 6)   := Twenty        (Low ..  High);             --  (12, 13, 14)
   A2 : Arr1 (9 .. 11)  := Same (Twenty) (1 .. 3);                   --  (1, 2, 3)
   A3 : Arr1 (11 .. 13) := Twenty        (Sub_Int);                  --  (5, 6, 7)
   A4 : Arr1 (1 .. 0)   := Twenty        (11 .. 10);                 --  Null slice
   A5 : Arr2 (One .. Thirty_Two) :=  Six_Four (Two ..  Sixty_Four);  --  (2, 4, 8, 16, 32, 64)

begin
   Put_Line ("Declaration");
   Put_Line ("");

   Put_Line ("A1: " & Boolean'Image (Is_Equal (A1, 12, 13, 14)));
   Put_Line ("A2: " & Boolean'Image (Is_Equal (A2, 1, 2, 3)));
   Put_Line ("A3: " & Boolean'Image (Is_Equal (A3, 5, 6, 7)));
   Put_Line ("A4: " & Boolean'Image (Is_Empty (A4)));
   Put_Line ("A5: " & Boolean'Image (Is_Equal (A5, 6, 6, 6, 6, 6, 6)));

   A1 (5 .. 5) := (5 => 1);                                           --  (12, 1, 14)
   A2 (2 .. 1) := (others => 1);                                      --  (1, 2, 3)
   A3 (A3'First .. A3'Last) := (for I in A3'Range => 1);              --  (1, 1, 1)
   A4 (20 .. 10) := (others => 20);                                   --  Empty
   A5 (Four .. Thirty_Two) := (Four | Thirty_Two => 4, others => 8);  --  (6, 6, 4, 8, 8, 4)

   Put_Line ("");
   Put_Line ("Assignment");
   Put_Line ("");

   Put_Line ("A1: " & Boolean'Image (Is_Equal (A1, 12, 1, 14)));
   Put_Line ("A2: " & Boolean'Image (Is_Equal (A2, 1, 2, 3)));
   Put_Line ("A3: " & Boolean'Image (Is_Equal (A3, 1, 1, 1)));
   Put_Line ("A4: " & Boolean'Image (Is_Empty (A4)));
   Put_Line ("A5: " & Boolean'Image (Is_Equal (A5, 6, 6, 4, 8, 8, 4)));
end Main;
