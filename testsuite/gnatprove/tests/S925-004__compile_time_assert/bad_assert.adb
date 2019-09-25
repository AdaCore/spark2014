with Global; use Global;

procedure Bad_Assert is
begin
   pragma Compile_Time_Error (X /= 42, "cannot assert X = 42");
   pragma Assert (X = 42);
end Bad_Assert;
