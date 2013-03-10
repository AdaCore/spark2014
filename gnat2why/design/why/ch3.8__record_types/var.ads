package Var is

   type Decision_Kind is
     (Condition_Kind,
      Not_Kind,
      Or_Else_Kind,
      And_Then_Kind);

   type Node_Id is range 1 .. 1000;

   type Decision (Kind : Decision_Kind := Condition_Kind) is record
      Id : Node_Id;

      case Kind is
         when Condition_Kind =>
            null;

         when Not_Kind =>
            Operand : Node_Id;

         when Or_Else_Kind | And_Then_Kind =>
            Left  : Node_Id;
            Right : Node_Id;
      end case;

   end record;

end Var;
