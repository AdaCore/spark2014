package T
  with SPARK_Mode
is
   procedure Update (X : in out Integer);
   task type TT is
   end TT;

   T1 : TT;
   T2 : TT;
end T;
