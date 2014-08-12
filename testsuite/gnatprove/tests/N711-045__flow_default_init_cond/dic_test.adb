procedure DIC_Test is
   package Pkg is
      type T is private with Default_Initial_Condition => Null;
   private
      type T is new Integer;
      package Nested is
         type T2 is private with Default_Initial_Condition => True;
      private
         type T2 is new T with Default_Value => 0;
      end;
   end;
begin
   null;
end DIC_Test;
