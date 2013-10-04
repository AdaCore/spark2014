with SM_Operations.SPARK;

package body SM_Operations is

   procedure Null_Op(Trigger : Triggers_T) is
   begin
      SPARK.Null_Op;
   end Null_Op;

   procedure Execute_Op(Op_Ptr: in Op_Ptr_T; Trigger : Triggers_T) is
   begin
      Op_Ptr.all(Trigger);
   end;

end SM_Operations;
