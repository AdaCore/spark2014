package Global_Derives_05
--# own X, Y: Integer;
is

   procedure Swap;
   --# global in out X, Y;
   --# derives X from Y &
   --#         Y from X;
   
   function Add return Integer;
   --# global in X, Y;
   
end Global_Derives_05;
