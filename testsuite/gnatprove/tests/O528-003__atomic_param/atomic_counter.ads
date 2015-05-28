package Atomic_Counter is
   type Atomic_Unsigned is mod 2 ** 32 with Default_Value => 0, Atomic;
   --  Modular compatible atomic unsigned type.
   --  Increment/Decrement operations for this type are atomic only on
   --  supported platforms. See top of the file.

   --  The "+" and "-" abstract routine provided below to disable BT := BT + 1
   --  constructions.

   function "+"
     (Left, Right : Atomic_Unsigned) return Atomic_Unsigned is abstract;

   function "-"
     (Left, Right : Atomic_Unsigned) return Atomic_Unsigned is abstract;

end Atomic_Counter;
