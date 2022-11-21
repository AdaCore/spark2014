with Pred;

package Use_Preds with SPARK_Mode is
   type List_Cell_3 is private;
   type List_3 is access List_Cell_3;

   function All_Pos (X : List_3) return Boolean with
     Subprogram_Variant => (Structural => X),
     Post => All_Pos'Result;
private
   type List_Cell_3 is record
      V : Pred.T;
      N : List_3;
   end record;

   function All_Pos (X : List_3) return Boolean is
     (X = null or else (Pred.Get (X.V) >= 0 and All_Pos (X.N)));
end;
