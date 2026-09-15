pragma Extensions_Allowed (All_Extensions);

procedure Test
  (Early_Low, Early_High :     Positive;
   First, Last, Length   : out Integer)
with
  SPARK_Mode,
  Pre     => Early_Low <= Early_High and then Early_High <= 3,
  Depends =>
    (First  => Early_Low,
     Last   => Early_High,
     Length => (Early_Low, Early_High))
is
   type Arr is array (Positive range <>) of Integer;

   Low  : constant Positive := Early_Low;
   High : constant Positive := Early_High;
   A    : Arr (Low .. High) := (others => 0);
begin
   <<Capture>>
   First := A'At (Capture)'First;
   Last := A'At (Capture)'Last;
   Length := A'At (Capture)'Length;
end Test;
