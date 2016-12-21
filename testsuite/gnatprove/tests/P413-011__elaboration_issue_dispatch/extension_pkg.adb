package body Extension_Pkg is
  function Op (X : Ext) return Boolean is
     pragma Assert (Body_Elaborated);
  begin
     return X.Flag;
  end;
begin
  Body_Elaborated := True;
end;
