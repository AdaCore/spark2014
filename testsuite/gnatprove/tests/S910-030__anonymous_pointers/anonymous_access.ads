package Anonymous_Access with SPARK_Mode is

   type List;
   type List_Acc is access List;
   type List is record
      V : Integer;
      N : List_Acc;
   end record;

   function Length (L : access List) return Natural is
     (if L = null then 0
      else Integer'Min (Natural'Last - 1, Length (L.N)) + 1)
   with Ghost,
     Annotate => (GNATProve, Terminating);

   function Copy (X : List_Acc) return List_Acc with
     Volatile_Function,
     Post => Length (Copy'Result) = Length (X);
end Anonymous_Access;
