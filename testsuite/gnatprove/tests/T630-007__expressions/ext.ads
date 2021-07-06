package Ext is
   type My_Char is new Character range 'b' .. 'z';

   Bad_Char : constant My_Char := 'a';

   type My_Enum is (L_1, L_2, L_3, L_4, L_5);
   type Small_Enum is new My_Enum range L_1 .. L_4;

   Bad_Enum : constant Small_Enum := L_5;
end Ext;
