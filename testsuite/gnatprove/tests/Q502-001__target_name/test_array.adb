procedure Test_Array with SPARK_Mode is
   type Nat_Array is array (Positive range <>) of Natural;
   subtype C_Arr is Nat_Array (1 .. 10);

   procedure P1 (X : in out Nat_Array) with
     Pre => X'First = 1 and X'Last >= 10
   is
   begin
      X (1 .. 3) := (1 => 0, others => @ (2));
      X (1) := @ + 1;
      X := (@ with delta 1 => @ (1), 3 .. 4 => @'Last);
   end P1;

   procedure P2 (X : in out C_Arr) with
     Pre => True
   is
   begin
      X (1 .. 3) := (1 => 0, others => @ (2));
      X (1) := @ + 1;
      X := (@ with delta 1 => @ (1), 3 .. 4 => @'Last);
   end P2;
begin
   null;
end Test_Array;
