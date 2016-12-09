package body Check_LSP with SPARK_Mode is
   package body  P_Overridden is
      function Get_F (X : Root) return Integer is
      begin
         return X.F;
      end Get_F;

      function Get_F (X : Child) return Integer is
      begin
         return X.G;
      end Get_F;

      function Get_F (X : Grand_Child) return Integer is
      begin
         return X.H;
      end Get_F;
   end P_Overridden;

   package body P_Inherited is
      function Get_F (X : Root) return Integer is
      begin
         return X.F;
      end Get_F;

      function Get_F (X : Grand_Child) return Integer is
      begin
         return X.H;
      end Get_F;
   end P_Inherited;
end Check_LSP;
