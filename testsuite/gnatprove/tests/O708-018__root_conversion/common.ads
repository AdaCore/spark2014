package Common is

   type My_Integer is new Integer;

   type My_Duration is new Duration;

   subtype My_Subduration is Duration range -10.0 .. 10.0;


end Common;
