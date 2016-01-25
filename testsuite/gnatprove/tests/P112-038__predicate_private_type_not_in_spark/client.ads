with Dyn_Pred2; use Dyn_Pred2;

package Client with SPARK_Mode is

   procedure P1 (X : Rec_Type);
   procedure P2 (X : Non_Zero_Type);
   procedure P3 (X : Positive_Subtype);

end;
