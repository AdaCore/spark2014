with Inner_Pkg;
package Probe with SPARK_Mode => On is

   type Outer is record
      I : Inner_Pkg.Inner (10);
   end record;

end Probe;
