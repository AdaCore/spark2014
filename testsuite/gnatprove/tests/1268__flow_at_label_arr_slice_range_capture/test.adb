pragma Extensions_Allowed (All_Extensions);

procedure Test
  (Early_Low, Early_High :     Positive;
   Late_Low, Late_High   :     Positive;
   Index                 :     Positive;
   O                     : out Boolean)
with
  SPARK_Mode,
  Pre =>
    Early_Low <= Early_High
    and then Early_High <= 3
    and then Late_Low <= Late_High
    and then Late_High <= 3,
  Depends =>
    (O    => (Early_Low, Early_High, Index),
     null => (Late_Low, Late_High))
is
   type Arr is array (Positive range 1 .. 3) of Integer;

   A    : Arr := (others => 0);
   Low  : Positive := Early_Low;
   High : Positive := Early_High;
begin
   <<Capture>>
   Low := Late_Low;
   High := Late_High;
   O := Index in A (Low .. High)'At (Capture)'Range;
end Test;
