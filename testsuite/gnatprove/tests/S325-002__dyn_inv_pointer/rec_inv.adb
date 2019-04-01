procedure Rec_Inv with SPARK_Mode is
   type List_D;

   type List_Acc is access List_D;

   type List_D (D : Boolean) is record
      Val  : Integer;
      Next : List_Acc;
   end record
     with Predicate => (if D then Val > 0);

   function F (X : List_Acc) return Integer is
     (X.Val)
     with Pre => X /= null,
     Post => (if X.D then F'Result > 0);

   function G (X : List_Acc) return Integer is
     (X.Next.Val)
     with Pre => X /= null and then X.Next /= null,
     Post => (if X.Next.D then G'Result > 0);

   function H (X : List_Acc) return Integer is
     (X.Next.Val)
     with Pre => X /= null and then X.Next /= null,
     Post => H'Result > 0; --@POSTCONDITION:FAIL

   function I (X : List_Acc) return Integer is
     (X.Next.Next.Val)
     with Pre => X /= null and then X.Next /= null and then X.Next.Next /= null,
     Post => (if X.Next.Next.D then I'Result > 0);

   X : List_D (True) := (True, 1, null);
begin
   X.Next := new List_D'(False, -2, null);
end Rec_Inv;
