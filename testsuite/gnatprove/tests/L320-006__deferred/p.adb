procedure P is
    package Pack is
       type T1 is record
          X : Boolean;
       end record;
       subtype T2 is T1;
       X1 : constant T1;
       X2 : T2 := (X => True);
    private
       X1 : constant T1 := X2;
    end Pack;
begin
    null;
end P;
