package Base.Ext with
  SPARK_Mode
is
   type U is new T with private;
private
   type U is new T with record
      D : Integer;
   end record;

   function Sum (X : U) return Integer is (X.C + X.D);

   function Create (C : Integer) return U is (T'(Create (C)) with D => 0);

end Base.Ext;
