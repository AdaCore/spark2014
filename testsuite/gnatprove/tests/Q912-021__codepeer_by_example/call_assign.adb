with Assign, Cond_Assign, Self_Assign;
package body Call_Assign is
   procedure Call (X : in out Integer; C : in Choice) is
   begin
      case C is
         when Simple =>
            Assign (X, 1);
         when Conditional =>
            Cond_Assign (X, 2, True);
         when Self =>
            Self_Assign (X);
      end case;
   end Call;
end Call_Assign;
