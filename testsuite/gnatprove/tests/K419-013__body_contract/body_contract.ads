package Body_Contract is

   procedure P1 (X : in out Integer);

   procedure P3 (X : in out Integer) with
     Pre  => X > 0,
     Post => X = X'Old - 1;

end Body_Contract;
