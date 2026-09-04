pragma Extensions_Allowed (All_Extensions);

procedure Qualified
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
   type Arr is array (Positive range <>) of Integer;

   Low  : Positive := Early_Low;
   High : Positive := Early_High;
   A    : Arr := (Low .. High => 0);
begin
   <<Capture>>
   Low := Late_Low;
   High := Late_High;
   First := Arr'(A (Low .. High)'At (Capture))'First;
   Last := Arr'(A (Low .. High)'At (Capture))'Last;
end;
