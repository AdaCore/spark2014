with test_package.ghost; use test_package.ghost;

package body test_package
with
Refined_State => ( test_state => ( Global_Ghost_a, Global_Ghost_b, Global_Ghost_new ) ),
  SPARK_Mode => On
is

   procedure test_func
     with
   --Refined_Pre => test_func_pre_success_state,
     Refined_Post => test_func_post_success_state
   is
   begin
      Global_Ghost_a := True;
      Global_Ghost_b := True;
      Global_a := True;
   end test_func;

   procedure test_func_new
     with
   --Refined_Pre => test_func_new_pre_success_state,
     Refined_Post => test_func_new_post_success_state
   is
   begin
      Global_Ghost_new := True;
   end test_func_new;

   package body spec is

      function test_func_pre_success_state
        return Boolean
      is
        ( ghost.test_func_pre_success_state );

      function test_func_post_success_state
        return Boolean
      is
        ( ghost.test_func_post_success_state );

      function test_func_new_pre_success_state
        return Boolean
      is
        ( ghost.test_func_new_pre_success_state );

      function test_func_new_post_success_state
        return Boolean
      is
        ( ghost.test_func_new_post_success_state );

   end spec;

end test_package;
