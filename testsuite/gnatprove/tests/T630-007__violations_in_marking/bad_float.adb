procedure Bad_Float with SPARK_Mode is
   package Mode_Off with SPARK_Mode => Off is
      type Bad_Fixed is delta 0.05 range -100.0 .. 100.0;
      X : constant Bad_Fixed := 0.0;
      Y : constant Bad_Fixed := 10.0;
   end Mode_Off;

   type My_Fixed is delta 0.05 range -100.0 .. 100.0;
   X : constant My_Fixed := 0.0;
   Y : constant My_Fixed := 10.0;
   type My_Float is digits 6 range X .. Y;
   type My_Float_2 is digits 6 range Mode_Off.X .. Mode_Off.Y;
begin
   null;
end Bad_Float;
