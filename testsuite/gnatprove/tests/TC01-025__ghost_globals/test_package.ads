package test_package
with
Abstract_State => test_state,
  Initializes => ( Global_a, test_state ),
  Initial_Condition => spec.test_func_pre_success_state,
  SPARK_Mode => On
is
   pragma Elaborate_Body;
   
   Global_a : Boolean := False;
   
   procedure test_func
     with
       Global => ( In_Out => ( test_state, Global_a ) ),
       Pre => spec.test_func_pre_success_state,
       Post => spec.test_func_post_success_state;
   
   procedure test_func_new
     with 
       Global => ( In_Out => ( test_state ), Proof_In => Global_a ),
       Pre => spec.test_func_new_pre_success_state,
       Post => spec.test_func_new_post_success_state;   
   
   package spec with ghost is
   
      function test_func_pre_success_state 
        return Boolean
      with Global => (Input => ( test_state, Global_a ) );        
   
      function test_func_post_success_state 
        return Boolean
      with Global => (Input => ( test_state, Global_a ) );
   
      function test_func_new_pre_success_state 
        return Boolean
      with Global => (Input => ( test_state, Global_a ) );
      
      function test_func_new_post_success_state 
        return Boolean
      with Global => (Input => ( test_state ) );
      
   end spec;
   
end test_package;
