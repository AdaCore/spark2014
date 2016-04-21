with Object; use Object;
with Derived; use Derived;

procedure Dispatcher is
   Var  : D := (B => False);
   VarC : T'Class := T'Class (Var);
begin
   pragma Assert (VarC.Is_Valid);
   VarC.Do_Stuff;
end Dispatcher;
