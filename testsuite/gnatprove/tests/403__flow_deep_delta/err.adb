procedure Err (Y : out Integer)
   with SPARK_Mode
is
   type A1 is array (Integer range 1 .. 3) of Integer;
   type A2 is array (Integer range 1 .. 3) of A1;
   type A3 is array (Integer range 1 .. 3) of A2;
   Tmp : A3 := (others => (others => (others => 0)));
   A, B, C : Integer;
begin
   Tmp := (Tmp with delta (A) (B) => (others => C));
   Y := Tmp (1) (1) (1);
end;
