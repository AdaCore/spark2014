--  PantherChess - based on AdaChess Copyright (C) 2017-2018 Bill Zuercher


package AChess is

   ----------------------------------------
   -- Type definitions and configuration --
   ----------------------------------------

   type Integer_Type is range - 2 ** 25 .. 2 ** 25 - 1 with Size => 26;

   Infinity : constant Integer_Type := Integer_Type'Last;

   type Color_Type is (White, Black) with Size => 2;

   -- define a function to swap colors
   function "not" (Color : in Color_Type) return Color_Type is
     (if Color = White then Black else White);


   -- Convert an Integer_Type to its String representation
   function To_String
     (Value : in Integer_Type) return String is (Integer_Type'Image (Value));

   -- The Node_Type will count how many operations the engine
   -- can perform in a certain amount of time.
   type Node_Type is mod 2 ** 64 with Size => 64;


end AChess;
