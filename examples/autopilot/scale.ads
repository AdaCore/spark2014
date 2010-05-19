with Instruments,Degrees,Surfaces;
--# inherit Instruments, Degrees, Surfaces;
package Scale
is
   subtype Scaledata is Integer range -100..100;
   
   -- Scale a control movement with respect to current
   -- speed and data differences
   function Scale_Movement(Mach : Instruments.Machnumber;
			   Present : in Scaledata;
			   Target  : in Scaledata;
			   Max     : in Surfaces.ControlAngle)
			  return Surfaces.ControlAngle;
   --# pre (Max > 0);
   --# return M => ( (-Max <= M) and (M <= Max) );
   
   -- Give a relative steering offset from Present to Target
   --  (turns to port are given as >= 180 degrees)
   function Heading_Offset(Present : Instruments.Headdegree;
   			   Target  : Instruments.Headdegree)
			  return Instruments.Headdegree;
    
end Scale;


  
  
  
