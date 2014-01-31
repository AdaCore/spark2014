with Degrees, Instruments, Surfaces;
use  Surfaces;

package Scale is
   subtype Scaledata is Integer range -100 .. 100;

   -- Scale a control movement with respect to current
   -- speed and data differences
   function Scale_Movement
     (Mach    : Instruments.Machnumber;
      Present : in Scaledata;
      Target  : in Scaledata;
      Max     : in Surfaces.Controlangle)
      return    Surfaces.Controlangle
     with Pre  => Max > 0,
          Post => -Max <= Scale_Movement'Result
                    and Scale_Movement'Result <= Max;

   -- Give a relative steering offset from Present to Target
   --  (turns to port are given as >= 180 degrees)
   function Heading_Offset
     (Present : Instruments.Headdegree;
      Target  : Instruments.Headdegree)
      return    Instruments.Headdegree;
end Scale;
