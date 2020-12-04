private package test_package.ghost
with
SPARK_Mode => On,
  Initial_Condition => Global_Ghost_a = False and then Global_Ghost_b = False and then Global_Ghost_new = False,
  ghost
is

   Global_Ghost_a : Boolean := False with Part_Of => test_state;
   Global_Ghost_b : Boolean := False with Part_Of => test_state;
   Global_Ghost_new : Boolean := False with Part_Of => test_state;

   function test_func_pre_success_state
     return Boolean
   is
     ( Global_Ghost_a = false and then
      Global_Ghost_b = false and then
      Global_a = false );

   function test_func_post_success_state
     return Boolean
   is
     ( Global_Ghost_a = True and then
      Global_Ghost_b = True and then
      Global_a = True );

   function test_func_new_pre_success_state
     return Boolean
   is
     ( Global_Ghost_new = false and then
      test_func_post_success_state );

   function test_func_new_post_success_state
     return Boolean
   is
     ( Global_Ghost_new = True );

end test_package.ghost;
