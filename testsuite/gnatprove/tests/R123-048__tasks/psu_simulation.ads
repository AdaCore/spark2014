pragma Profile (Ravenscar);
with Ada.Real_Time;
package PSU_Simulation is

   type Sim_Config_T is record
      L1     : Float := 1.0e-3;  --  Inductance of L1
      C1     : Float := 1.0e-3;  --  Capacity of C1
      L2     : Float := 1.0e-3;  --  Inductance of L2
      C2     : Float := 1.0e-3;  --  Capacity of C2
      f_V1   : Float := 0.0;     --  Frequency of V1
      Up_V1  : Float := 1.0e+2;  --  Peak Voltage of V1
      T      : Float := 1.0e-3;  --  Time for simulation step
   end record;

   type Sim_Output_T is record
      I_L1   : Float := 0.0;     --  Current through L1
      I_L2   : Float := 0.0;     --  Current through L2
      I_Load : Float := 0.0;     --  Current through Load
      U_C1   : Float := 0.0;     --  Voltage over C1
      U_C2   : Float := 0.0;     --  Voltage over C2
      U_V1   : Float := 0.0;     --  Voltage of V1
   end record;

   maxLoadValues : constant Integer := 20; -- Constant max number of load values
   type loadArray_T is array (Integer range 1 .. maxLoadValues, Integer range 1 .. 2) of Float;

   protected type Simulation_I_T is
      function  Is_Ready return Boolean;                --  Synchronize threads at startup (returns true when everything is configured)
      function  Get_Config return Sim_Config_T;         --  Get the hardware configuration of this simulation
      function  Get_I_L1 return Float;                  --  Get the current through L1
      function  Get_I_L2 return Float;                  --  Get the current through L2
      function  Get_I_Load return Float;                --  Get the current through Load
      function  Get_U_C1 return Float;                  --  Get the voltage over C1
      function  Get_U_C2 return Float;                  --  Get the voltage over C2
      function  Get_U_V1 return Float;                  --  Get the voltage of V1
      function  Get_Sim_All return Sim_Output_T;        --  Get all output values
      function  Get_D_M1 return Float;                  --  Get the dutycycle for M1
      function  Get_D_M2_5 return Float;                --  Get the dutycycle for M2 to M5
      function  Get_Load return loadArray_T;            --  Get the load configuration
      procedure Set_Config (Val : in Sim_Config_T);     --  Set the hardware configuration of this simulation
      procedure Set_D_M1 (Val : in Float);              --  Set the dutycycle for M1
      procedure Set_D_M2_5 (Val : in Float);            --  Set the dutycycle for M2 to M5
      procedure Set_Sim_Out (Val : in Sim_Output_T);    --  Set all output values
      procedure Set_Load (Val : in loadArray_T);        --  Set the load configuration
   private
      Sim_Out   : Sim_Output_T;      --  Buffer
      D_M2_5    : Float := 0.0;      --  Buffer
      D_M1      : Float := 0.0;      --  Buffer
      Conf      : Sim_Config_T;      --  Buffer
      Loads     : loadArray_T;       --  Buffer
      Conf_OK   : Boolean := False;  --  Status of initilization (true when configuration is set)
      Load_OK   : Boolean := False;  --  Status of initilization (true when load is set)
   end Simulation_I_T;

   Sim : Simulation_I_T;  --  Instantiation of Interface

private

   task type Simulation_Task_T is
   end Simulation_Task_T;

   function Get_Load_Actual (ST : Ada.Real_Time.Time; LO : loadArray_T) return Float;

end PSU_Simulation;
