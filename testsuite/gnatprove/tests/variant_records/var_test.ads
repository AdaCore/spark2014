with Tristates; use Tristates;
with Var; use Var;

package Var_Test is

   Decision_Table   : array (Node_Id) of Decision;
   Condition_Values : array (Node_Id) of Tristate;

   function Decision_Eval
     (Root_Id : Node_Id)
     return Tristate
     with Pre => (for all X in Node_Id'Range => Condition_Values (X) /=
        T_Unknown),
          Post => (Decision_Eval'Result /= T_Unknown);

end Var_Test;
