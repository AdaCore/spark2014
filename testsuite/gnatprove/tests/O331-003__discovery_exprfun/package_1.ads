package Package_1
with SPARK_Mode => On
is
   subtype Restricted_Float is Float range -100.0 .. 100.0;

   procedure Update (InputVar  : in     Restricted_Float;
                     OutputVar :    out Float);

end Package_1;
