package body Test
is

   --  Thing          Unint  Pre     Post
   --  =============  =====  ======  ====
   --  in     param       -
   --  in out param       -
   --     out param       y  static  flow
   --  in     global      -
   --  in out global      -
   --     out global      y  static  flow
   --  in     gg          -
   --  in out gg          -
   --     out gg      NOT SUPPORTED YET
   --
   --  So we need to only check for out parameters and out
   --  globals. Everything else must be initialised, if it is not, it
   --  is already detected. We will have one example to demonstrate
   --  this as well.
   --
   --  static: Any use is clearly a violation and can be just
   --     rejected. We need to do this in flow analyis as we need to
   --     be aware of globals read by any function calls.
   --
   --  flow: Existing flow analysis will make sure this is set once
   --     the subprogram returns.

   G : Integer;

   procedure T_In_Out_Param (X : in out Integer)
   with Pre => X > 0,
        Post => X > 0
   is
   begin
      null;
   end T_In_Out_Param;

   procedure Detect_Uninitialised_In_Out (V : out Integer)
   is
   begin
      --  This picks up that X > 0 in the contracts will refer to an
      --  uninitialized variable. (use of uninitialized variable "V").
      T_In_Out_Param (V);
   end Detect_Uninitialised_In_Out;

   procedure T_Out_Param (X : out Integer)
   with Pre => X > 0,
        Post => X > 0
   is
   begin
      --  We detect the uninitialised read in the postcondition
      --  indirectly in the flow analysis of the program (formal
      --  parameter "X" might not be set)
      null;
   end T_Out_Param;

   procedure T_Out_Global
   with Global => (Output => G),
        Pre => G > 0,
        Post => G > 0
   is
   begin
      --  We detect the uninitialised read in the postcondition
      --  indirectly in the flow analysis of the program (global "G"
      --  might not be set)
      null;
   end T_Out_Global;

   procedure Multiple_Preconditions (X, Y, Z : Integer)
   with Pre => X >= 0 and then Y >= 0
   is
      pragma Precondition (Z >= 0);
   begin
      null;
   end Multiple_Preconditions;

end Test;
