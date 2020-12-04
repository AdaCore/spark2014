with test_package; use test_package;

package caller_package
with
Abstract_State => caller_state,
  Initializes => ( Global_b, caller_state ),
  Initial_Condition => spec.caller_func_pre_success_state,
  SPARK_Mode => On
is
   pragma Elaborate_Body;
   
   Global_b : Boolean := False;
   
   procedure caller_func
     with
       Global => ( In_Out => ( Global_a, Global_b, caller_state, test_state ) ),
       Pre => spec.caller_func_pre_success_state,
       Post => spec.caller_func_post_success_state;

   package spec with ghost is
   
      function caller_func_pre_success_state 
        return Boolean;
   
      function caller_func_post_success_state 
        return Boolean;
      
   end spec;
   
end caller_package;
