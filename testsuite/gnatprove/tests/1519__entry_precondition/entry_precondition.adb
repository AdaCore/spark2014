package body Entry_Precondition with SPARK_Mode is
   protected body Gate is
      entry Enter (X : Integer) when Open is
      begin
         pragma Assert (X > 0);
      end Enter;
   end Gate;

   protected body Closed_Gate is
      entry Enter (X : Integer) when False is
      begin
         null;
      end Enter;
   end Closed_Gate;
end Entry_Precondition;
