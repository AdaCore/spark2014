package Loops with SPARK_Mode is
   type Nat_Array is array (Positive range <>) of Natural;

   procedure Loop1 (A : in out Nat_Array);

   procedure Loop2 (A : in out Nat_Array);

   procedure Loop3 (A : in out Nat_Array; Bad : out Boolean);

   procedure Loop4 (A : in out Nat_Array; Bad : out Boolean);
end Loops;
