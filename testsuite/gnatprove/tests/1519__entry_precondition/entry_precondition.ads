pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

package Entry_Precondition with SPARK_Mode is
   protected type Gate is
      entry Enter (X : Integer) with Pre => X > 0;
   private
      Open : Boolean := False;
   end Gate;

   --  The precondition is satisfiable, but its conjunction with the entry
   --  barrier is not.
   protected type Closed_Gate is
      entry Enter (X : Integer) with Pre => X > 0;
   end Closed_Gate;
end Entry_Precondition;
