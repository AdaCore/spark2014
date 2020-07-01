package Ext with SPARK_Mode is
   package Nested is
      type My_Rec is private;
      function Same_Discrs (X, Y : My_Rec) return Boolean;
   private
      type My_Rec (D : Boolean := True) is record
         F : Integer;
      end record;
      function Same_Discrs (X, Y : My_Rec) return Boolean is
        (X.D = Y.D);
   end Nested;

   Vol : Nested.My_Rec with Volatile;
end Ext;
