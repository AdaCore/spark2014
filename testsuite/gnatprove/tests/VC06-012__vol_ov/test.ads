package Test is

   type T is new Integer;

   X : Integer with Volatile ;
   Y : Integer := 0 with Address => X'Address;

   U : Integer;
   V : Integer := 0 with Address => U'Address, Volatile;

   A : Integer;
   B : Integer := 0 with Address => A'Address, Atomic;

   C : Integer with Atomic;
   D : Integer := 0 with Address => C'Address;

   E : Integer with Atomic;
   F : Integer := 0 with Address => E'Address, Atomic;
end Test;
