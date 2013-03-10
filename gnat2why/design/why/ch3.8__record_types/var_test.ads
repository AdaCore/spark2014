with Tristates; use Tristates;
with Var; use Var;

package Var_Test is

   Decision_Table   : array (Node_Id) of Decision;
   Condition_Values : array (Node_Id) of Tristate;

   function Decision_Eval
     (Root_Id : Node_Id)
     return Tristate;
   --  ???  Quantifiers in Ada 2012 are not fully designed yet, but
   --  they would look like that:
   --  pragma Precondition (for all X in Node_Id'Range |
   --                       Condition_Values (X) /= T_Unknown);
   pragma Postcondition (Decision_Eval'Result /= T_Unknown);

end Var_Test;
