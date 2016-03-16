package body P with SPARK_Mode is

   protected body PT is
      procedure Proc is
         function Id (X : Boolean) return Boolean is (X);

         Dummy_From_Same_PT  : Boolean := Id (PT.F);
         Dummy_From_Other_PT : Boolean := Id (Other.G);
      begin
         null;
      end;

      function F return Boolean is (True);

   end;

   protected body Other is
      function G return Boolean is (False);
   end;

end;
