package P is
   type R (Discr : Boolean) is private;

private
   pragma SPARK_Mode (Off);
   type R (Discr : Boolean) is null record;
end P;
