package body Initializes_Legal
  with SPARK_Mode,
       Refined_State => (AS  => (Y, Z),
                         AS2 => (L, M))
is
   Z : Integer;
   Y : Integer := Init.Sum_State;
   L : Integer := Init.A;
   M : Integer;

   function Add (X, Y : Integer) return Integer is (X + Y);
begin
   Z := 0;
   M := Init.Sum_State;
   X := Add (Y, L);
end Initializes_Legal;
