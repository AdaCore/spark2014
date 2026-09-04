pragma Extensions_Allowed (All_Extensions);

procedure Direct
  (Early_Low, Early_High :     Positive;
   Late_Low, Late_High   :     Positive;
   First, Last           : out Integer)
with
  SPARK_Mode,
  Pre =>
    Early_Low <= Early_High
    and then Early_High <= 3
    and then Late_Low <= Late_High
    and then Late_High <= 3,
  Depends =>
    (First => Early_Low,
     Last  => Early_High,
     null  => (Late_Low, Late_High))
is
   type Arr is array (Positive range 1 .. 3) of Integer;

   A    : Arr := (others => 0);
   Low  : Positive := Early_Low;
   High : Positive := Early_High;
begin
   <<Capture>>
   Low := Late_Low;
   High := Late_High;
   First := A (Low .. High)'At (Capture)'First;
   Last := A (Low .. High)'At (Capture)'Last;
end;
