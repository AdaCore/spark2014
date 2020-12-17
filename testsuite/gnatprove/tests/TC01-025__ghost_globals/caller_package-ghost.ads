with test_package; use test_package.spec;

private package caller_package.ghost
with
SPARK_Mode => On, ghost,
  Initial_Condition => ( Global_Ghost_c = False and then Global_Ghost_d = False )
is
   
   Global_Ghost_c : Boolean  := False with Part_Of => caller_state;
   Global_Ghost_d : Boolean  := False with Part_Of => caller_state;
   
   function caller_func_pre_success_state 
     return Boolean
   is
     ( test_func_pre_success_state and then 
      Global_Ghost_c = False and then
      Global_Ghost_d = False and then
      Global_b = False );
   
   function caller_func_post_success_state 
     return Boolean
   is
     ( test_func_post_success_state and then
      test_func_new_post_success_state and then
      Global_Ghost_c = True and then
      Global_Ghost_d = True and then
      Global_b = True);
   
end caller_package.ghost;
