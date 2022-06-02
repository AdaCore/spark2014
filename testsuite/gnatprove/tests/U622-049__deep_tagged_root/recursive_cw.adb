procedure Recursive_CW with SPARK_Mode is
   type Root is tagged;
   type Root_Acc is access Root'Class;
   type Root is tagged record
      V : Integer;
      Next : Root_Acc;
   end record;

   function All_Less_Than (X : access constant Root'Class; V : Integer) return Boolean is
     (if X = null then True else X.V < V and then All_Less_Than (X.Next, V))
   with Annotate => (GNATprove, Always_Return);

   X : aliased Root'Class := Root'(1, new Root'(2, new Root'(3, new Root'(4, null))));
begin
   declare
      B : access Root'Class := X'Access;
   begin
      while B /= null loop
         pragma Loop_Invariant (All_Less_Than (B, 5));
         B.V := B.V + 1;
         B := B.Next;
      end loop;
   end;
end;
