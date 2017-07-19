package Loops_Static with SPARK_Mode is
   type Nat_Array is array (Integer range <>) of Natural;

   procedure Loop1 (A : in out Nat_Array);

   procedure Loop2 (A : in out Nat_Array);

   procedure Loop3 (A : in out Nat_Array; Bad : out Boolean);

   procedure Loop4 (A : in out Nat_Array; Bad : out Boolean);

   procedure Loop5 (A : in out Nat_Array; Bad : out Boolean);

   procedure Loop6 (A : in out Nat_Array; Bad : out Boolean);

   procedure Loop7 (A : in out Nat_Array; Bad : out Boolean);

   procedure Loop8 (A : in out Nat_Array; Bad : out Boolean);

--   function Loop9 (A : Nat_Array) return Boolean;

   function Loop10 (A : Nat_Array) return Nat_Array;
end Loops_Static;
