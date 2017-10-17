package Call_Assign is
   type Choice is (Simple, Conditional, Self);
   procedure Call (X : in out Integer; C : in Choice);
end Call_Assign;
