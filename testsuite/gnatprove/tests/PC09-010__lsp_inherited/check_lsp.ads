package Check_LSP with SPARK_Mode is
   package P_Overridden is
      type Root is tagged record
         F : Integer;
      end record;

      function Get_F (X : Root) return Integer with
        Post'Class => Get_F'Result = X.F; --@POSTCONDITION:FAIL

      type Child is new Root with record
         G : Integer;
      end record;

      function Get_F (X : Child) return Integer;

      type Grand_Child is new Child with record
         H : Integer;
      end record;

      function Get_F (X : Grand_Child) return Integer;
   end P_Overridden;

   package P_Inherited is
      type Root is tagged record
         F : Integer;
      end record;

      function Get_F (X : Root) return Integer with
        Post'Class => Get_F'Result = X.F; --@POSTCONDITION:FAIL

      type Child is new Root with record
         G : Integer;
      end record;

      type Grand_Child is new Child with record
         H : Integer;
      end record;

      function Get_F (X : Grand_Child) return Integer;
   end P_Inherited;
end Check_LSP;
