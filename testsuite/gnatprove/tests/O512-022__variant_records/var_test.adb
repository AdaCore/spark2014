with Tristates; use Tristates;
with Var; use Var;

package body Var_Test is

   function Decision_Eval
     (Root_Id : Node_Id)
     return Tristate is
      D    : Decision      := Decision_Table (Root_Id);
      Kind : Decision_Kind := D.Kind;
   begin
      case Kind is
         when Condition_Kind =>
            return Condition_Values (D.Id);
         when Not_Kind =>
            return T_Not (Decision_Eval (D.Operand));
         when Or_Else_Kind =>
            return T_Or (Decision_Eval (D.Left), Decision_Eval (D.Right));
         when And_Then_Kind =>
            return T_And (Decision_Eval (D.Left), Decision_Eval (D.Right));
      end case;
   end Decision_Eval;

end Var_Test;
