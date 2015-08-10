with Types; use Types;
with Pid_Parameters; use Pid_Parameters;

generic
   INPUT_LOW_LIMIT   : Float;
   INPUT_HIGH_LIMIT  : Float;
   OUTPUT_LOW_LIMIT  : Float;
   OUTPUT_HIGH_LIMIT : Float;
   COEFF_LOW_LIMIT   : Float;
   COEFF_HIGH_LIMIT  : Float;

package Pid_Pack
with SPARK_Mode
is
   --  Subtypes for inputs/outputs of the PID
   subtype T_Input  is Float range INPUT_LOW_LIMIT .. INPUT_HIGH_LIMIT;
   subtype T_Output is Float range OUTPUT_LOW_LIMIT .. OUTPUT_HIGH_LIMIT;
   subtype T_Error  is Float range
     2.0 * INPUT_LOW_LIMIT .. 2.0 * INPUT_HIGH_LIMIT;
   subtype T_Deriv  is Float range
     4.0 * INPUT_LOW_LIMIT / T_Delta_Time'First ..
       4.0 * INPUT_HIGH_LIMIT / T_Delta_Time'First;
   subtype T_I_Limit is Float range
     -DEFAULT_PID_INTEGRATION_LIMIT .. DEFAULT_PID_INTEGRATION_LIMIT;
   subtype T_Coeff is Float range COEFF_LOW_LIMIT .. COEFF_HIGH_LIMIT;

   --  Types
   type Pid_Object is record
      Desired      : T_Input;       --  Set point
      Error        : T_Error;       --  Error
      Prev_Error   : T_Error;       --  Previous Error
      Integ        : T_I_Limit;     --  Integral
      Deriv        : T_Deriv;       --  Derivative
      Kp           : T_Coeff;       --  Proportional Gain
      Ki           : T_Coeff;       --  Integral Gain
      Kd           : T_Coeff;       --  Derivative Gain
      Out_P        : T_Output;      --  Proportional Output (debug)
      Out_I        : T_Output;      --  Integral Output (debug)
      Out_D        : T_Output;      --  Derivative Output (debug)
      I_Limit_Low  : T_I_Limit;     --  Limit of integral term
      I_Limit_High : T_I_Limit;     --  Limit of integral term
      Dt           : T_Delta_Time;  --  Delta Time
   end record;
   pragma Convention (C, Pid_Object);

   --  Procedures and Functions

   --  PID object initialization.
   procedure Pid_Init
     (Pid           : out Pid_Object;
      Desired       : T_Input;
      Kp            : T_Coeff;
      Ki            : T_Coeff;
      Kd            : T_Coeff;
      I_Limit_Low   : T_I_Limit;
      I_Limit_High  : T_I_Limit;
      Dt            : T_Delta_Time);

   --  Reset the PID error values.
   procedure Pid_Reset (Pid : in out Pid_Object);

   --  Update the PID parameters. Set 'UpdateError' to 'False' is error
   --  has been set previously for a special calculation with 'PidSetError'.
   procedure Pid_Update
     (Pid          : in out Pid_Object;
      Measured     : T_Input;
      Update_Error : Boolean)
     with
       Depends => (Pid => (Measured, Pid, Update_Error));

   --  Return the PID output. Must be called after 'PidUpdate'.
   function Pid_Get_Output (Pid : Pid_Object) return Float;

   --  Find out if the PID is active.
   function Pid_Is_Active (Pid : Pid_Object) return Boolean;

   --  Set a new set point for the PID to track.
   procedure Pid_Set_Desired
     (Pid     : in out Pid_Object;
      Desired : T_Input)
     with
       Post => Pid = Pid'Old'Update (Desired => Desired);

   --  Get the PID desired set point.
   function Pid_Get_Desired (Pid : Pid_Object) return Float;

   --  Set the new error. Used if special calculation is needed.
   procedure Pid_Set_Error
     (Pid   : in out Pid_Object;
      Error : T_Error)
     with
       Post => Pid = Pid'Old'Update (Error => Error);

   --  Set a new proprtional gain for the PID.
   procedure Pid_Set_Kp
     (Pid : in out Pid_Object;
      Kp  : T_Coeff)
     with
       Post => Pid = Pid'Old'Update (Kp => Kp);

   --  Set a new integral gain for the PID.
   procedure Pid_Set_Ki
     (Pid : in out Pid_Object;
      Ki  : T_Coeff)
     with
       Post => Pid = Pid'Old'Update (Ki => Ki);

   --  Set a new derivative gain for the PID.
   procedure Pid_Set_Kd
     (Pid : in out Pid_Object;
      Kd  : T_Coeff)
     with
       Post => Pid = Pid'Old'Update (Kd => Kd);

   --  Set a new low limit for the integral term.
   procedure Pid_Set_I_Limit_Low
     (Pid          : in out Pid_Object;
      I_Limit_Low  : T_I_Limit)
     with
       Post => Pid = Pid'Old'Update (I_Limit_Low => I_Limit_Low);

   --  Set a new high limit for the integral term.
   procedure Pid_Set_I_Limit_High
     (Pid           : in out Pid_Object;
      I_Limit_High  : T_I_Limit)
     with
       Post => Pid = Pid'Old'Update (I_Limit_High => I_Limit_High);

   --  Set a new dt gain for the PID. Defaults to
   --  IMU_UPDATE_DT upon construction.
   procedure Pid_Set_Dt
     (Pid : in out Pid_Object;
      Dt  : T_Delta_Time)
     with
       Post => Pid = Pid'Old'Update (Dt => Dt);

end Pid_Pack;
