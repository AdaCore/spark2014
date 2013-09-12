procedure P is pragma SPARK_Mode (On); 
   type T is record
      Access_Count : Natural := 0;
      Locked       : Boolean := False;
   end record with
     Predicate => (T.Locked = (T.Access_Count > 3));

   procedure Bad (V : in out T) is
   begin
      V.Access_Count := V.Access_Count + 1;
      V.Locked := True;
   end Bad;

   Var : T;  --  predicate checked at object creation
begin
   --  predicate checked when passing Var as input
   Bad (Var);
   --  predicate checked when returning Var as output
end P;
