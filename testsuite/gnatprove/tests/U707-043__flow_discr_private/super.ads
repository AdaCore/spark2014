package Super with SPARK_Mode is

   type Sup (Max : Positive) is record
      Cur : Natural := 0;
   end record;

   function Super_Id
     (Source : Sup) return Sup is (Source);

end Super;
