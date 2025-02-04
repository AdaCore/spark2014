procedure Main with SPARK_Mode is
   type Int_Acc_Cst is access constant Integer;
   function Create return Int_Acc_Cst with
     Import,
     Global => null,
     Post => Create'Result /= null and Create'Result.all = 2;
   procedure Observe (X : access constant Integer) with
     Import,
     Global => null,
     Always_Terminates;
   function Traverse  (X : access constant Integer) return access constant Integer with
     Import,
     Global => null,
     Contract_Cases =>
       (X = null => Traverse'Result = null,
        others   => Traverse'Result /= null and Traverse'Result.all = X.all);
   function Observe  (X : access constant Integer) return Integer with
     Import,
     Global => null,
     Post => (if X /= null then Observe'Result = 2);

   X : Integer := Observe (Traverse (Create));
begin
   Observe (Create);
   pragma Assert (X = 2);
end Main;
