package My_Pack with
   SPARK_Mode,
   Initializes       => X,
   Initial_Condition => X_True
is
   pragma Elaborate_Body;

   X : Boolean;
   function X_True return Boolean is (X);
end My_Pack;
