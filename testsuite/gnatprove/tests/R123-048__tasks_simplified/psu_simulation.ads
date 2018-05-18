pragma Profile (Ravenscar);

package PSU_Simulation is
   protected type Simulation is
      function Is_Ready return Boolean;
   end Simulation;
end PSU_Simulation;
