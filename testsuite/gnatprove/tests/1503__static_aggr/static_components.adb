procedure Static_Components with SPARK_Mode is
   subtype Small is Integer range -3 .. 5;
   type Int_Array is array (Positive range <>) of Small;
   Named : constant := 2;
   Ints : Int_Array := [-3, 5, Named, 1 + 2, Small'(4), Small (3)];

   type Byte is mod 256;
   subtype Small_Byte is Byte range 1 .. 4;
   type Byte_Array is array (Positive range <>) of Small_Byte;
   Bytes : Byte_Array := [1, 4, 2 + 1, Byte (3)];

   type Odd_Mod is mod 7;
   type Odd_Array is array (Positive range <>) of Odd_Mod;
   Odds : Odd_Array := [0, 6, 6 + 2];

   type Color is (Red, Green, Blue);
   for Color use (Red => 1, Green => 7, Blue => 50);
   subtype Some_Color is Color range Green .. Blue;
   type Color_Array is array (Positive range <>) of Some_Color;
   Colors : Color_Array := [Green, Blue, Color'Succ (Green)];

   subtype True_Only is Boolean range True .. True;
   type Bool_Array is array (Positive range <>) of True_Only;
   Bools : Bool_Array := [True, not False, 1 < 2];

   type Wide is mod 2 ** 64;
   type Wide_Array is array (1 .. 1) of Wide;
   Wides : Wide_Array := [Wide'Last];

   Updated : constant Byte_Array := [Bytes with delta 2 => 3];
   Iterated : constant Int_Array := [for I in 1 .. 3 => 4];
   Relaxed : Int_Array (1 .. 2) := [1, 2] with Relaxed_Initialization;
begin
   pragma Assert (Ints (1) = -3 and Ints (2) = 5 and Ints (4) = 3);
   pragma Assert (Bytes (3) = 3 and Odds (3) = 1);
   pragma Assert (Colors (1) = Green and Colors (3) = Blue and Bools (3));
   pragma Assert (Updated (1) = 1 and Updated (2) = 3);
   pragma Assert (Iterated (2) = 4);
   pragma Assert (Relaxed'Initialized and then Relaxed (2) = 2);
   pragma Assert (Wides (1) = Wide'Last);
end Static_Components;
