with caller_package; use caller_package;

procedure Main
  with
    SPARK_Mode => On,
    Pre => spec.caller_func_pre_success_state
is
begin
   caller_func;
end Main;
