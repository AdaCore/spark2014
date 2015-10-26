with Interfaces; use Interfaces;
procedure Badpre (RSP : Unsigned_64) with
  SPARK_Mode,
  Pre  => RSP in 16#FFFFFFFFFFFFFF00# + 1 .. 16#FFFFFFFF00000000# - 1,
  Post => False
is
begin
   null;
end Badpre;
