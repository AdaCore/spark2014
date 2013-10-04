with SM_Types; use SM_Types;

package SM_Operations
  with SPARK_Mode
is

   type Op_Ptr_T is private;

   Null_Op_Ptr : constant Op_Ptr_T;

   procedure Execute_Op(Op_Ptr : in Op_Ptr_T; Trigger : Triggers_T);

   procedure Null_Op(Trigger : Triggers_T);

private

   pragma SPARK_Mode(Off);
   type Op_Ptr_T is access procedure(Trigger : Triggers_T);

   Null_Op_Ptr : constant Op_Ptr_T := Null_Op'Access;

end SM_Operations;
