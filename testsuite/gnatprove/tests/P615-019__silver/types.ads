package Types is

   type Temperature is digits 6 range -100.0 .. 300.0;

   type Length is range 0 .. 65_535;

   type Temperature2 is new Float range -100.0 .. 300.0;

   type Length2 is new Integer range 0 .. 65_535;

   subtype Temperature3 is Float range -100.0 .. 300.0;

   subtype Length3 is Integer range 0 .. 65_535;

end Types;
