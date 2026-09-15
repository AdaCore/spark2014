pragma Extensions_Allowed (All_Extensions);

procedure Test
  (Before, After           :     Integer;
   Early_Low, Early_High   :     Positive;
   Late_Low, Late_High     :     Positive;
   Early_Index, Late_Index :     Positive;
   O                       : out Integer)
with
  SPARK_Mode,
  Pre =>
    Early_Low in 1 .. 3
    and then Early_High in 1 .. 3
    and then Early_Low <= Early_High
    and then Late_Low in 1 .. 3
    and then Late_High in 1 .. 3
    and then Late_Low <= Late_High
    and then Early_Index in 1 .. 3
    and then Late_Index in Early_Low .. Early_High,
  Depends =>
    (O    => (Before, Early_Low, Early_High, Late_Index),
     null => (After, Late_Low, Late_High, Early_Index))
is
   type Arr is array (Positive range 1 .. 3) of Integer;

   A     : Arr := (others => Before);
   Low   : Positive := Early_Low;
   High  : Positive := Early_High;
   Index : Positive := Early_Index;
begin
   <<Capture>>
   A := (others => After);
   Low := Late_Low;
   High := Late_High;
   Index := Late_Index;
   O := A (Low .. High)'At (Capture) (Index);
end Test;
