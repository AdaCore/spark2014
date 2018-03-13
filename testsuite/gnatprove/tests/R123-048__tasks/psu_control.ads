pragma Profile (Ravenscar);
package PSU_Control is

   --  This type provides settings for a PID controller
   type PID_Config_T is record
      Kp  : Float := 1.0;            --  P gain
      Ki  : Float := 1.0;            --  I gain (multiplied with Kp)
      Kd  : Float := 1.0;            --  D gain (multiplied with Kp)
      Sp  : Float := Float'Last;     --  Upper bound for saturation
      Sn  : Float := Float'First;    --  Lower bound for saturation
      T   : Float := 1.0;            --  Period time of calculation
   end record;

   type PID_Target_T is (PID_U_C1, PID_U_C2, PID_I_L1, PID_I_L2);
   type PID_Config_A_T is array (PID_Target_T)  of PID_Config_T;
   type PID_Config_Status_A_T is array (PID_Target_T) of Boolean;
   subtype Constraint_Float is Float range 0.0 .. 1.0;

   protected type Control_I_T is
      function Is_Ready return Boolean;
      function Get_Config return PID_Config_A_T;
      function Get_Config (Id : in PID_Target_T) return PID_Config_T;
      function Get_W_U_C1 return Float;
      function Get_W_U_C2 return Float;
      function Get_Safety_State return Boolean;
      procedure Set_Config (Val : in PID_Config_A_T);
      procedure Set_Config (Val : PID_Config_T; Id : PID_Target_T);
      procedure Set_W_U_C1 (Val : in Float);
      procedure Set_W_U_C2 (Val : in Float);
      procedure Set_Safety_State (Val : in Boolean);
   private
      W_U_C1       : Float := 0.0;
      W_U_C2       : Float := 0.0;
      Conf         : PID_Config_A_T;
      Conf_ALL_OK  : Boolean := False;
      Conf_State   : PID_Config_Status_A_T := (others => False);
      Safety_State : Boolean := False;
   end Control_I_T;
   Ctrl : Control_I_T;

   --  This type provides a PID controller
   --  Use of a tagged object would not be necesarry here
   type PID_Controller_T is tagged
      record
         Conf : PID_Config_T;
         E    : Float := 0.0;
         E1   : Float := 0.0;
         P    : Float := 0.0;
         I    : Float := 0.0;
         D    : Float := 0.0;
         Y    : Float := 0.0;
         Sat  : Float := 0.0;
      end record;
   function calculate_U
      (C : in out PID_Controller_T; W : in Float; Y : in Float)
       return Float;

   procedure reset (C : in out PID_Controller_T);

   type PID_Controller_A_T is array (PID_Target_T)  of PID_Controller_T;

   task type Control_Task_T is
   end Control_Task_T;

end PSU_Control;
