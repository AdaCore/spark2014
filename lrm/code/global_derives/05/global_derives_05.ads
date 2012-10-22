package global_derives_05
--# own X, Y: Integer;
is

   procedure Swap;
   --# global in out X, Y;
   --# derives X from Y &
   --#         Y from X;
   
   function Add return Integer;
   --# global in X, Y;
   
end global_derives_05;
