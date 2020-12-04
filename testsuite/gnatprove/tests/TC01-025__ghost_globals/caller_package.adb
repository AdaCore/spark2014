with caller_package.ghost; use caller_package.ghost;

package body caller_package
with
Refined_State => ( caller_state => ( Global_Ghost_c, Global_Ghost_d ) ),
  SPARK_Mode => On
is
   
   procedure caller_func
     with
   --Refined_Pre => caller_func_pre_success_state,
     Refined_Post => caller_func_post_success_state
   is
   begin
      test_func;
      test_func_new;
      Global_Ghost_c := True;
      Global_Ghost_d := True;
      Global_b := True;
   end caller_func;

   package body spec is
   
      function caller_func_pre_success_state 
        return Boolean
      is 
        ( ghost.caller_func_pre_success_state );
  
      function caller_func_post_success_state 
        return Boolean 
      is
         ( ghost.caller_func_post_success_state );
      
   end spec;
   
end caller_package;
