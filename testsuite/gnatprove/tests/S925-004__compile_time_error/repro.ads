generic
   type Item is private;
   Length : Positive;
package Repro is
   type Item_Array is array (1 .. Length) of Item;

   pragma Compile_Time_Error (Item_Array'Size /= 256, "Compile failed.");

   pragma Assert (Item_Array'Size = 256);
end Repro;
