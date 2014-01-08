with Binary_Fixed; use Binary_Fixed;

procedure Test_Binary_Fixed is
begin
   Test_Minus (0.0);
   Test_Minus (-5.0);
   Test_Minus (5.0);
   
   Test_Add (0.0);
   Test_Add (-5.0);
   Test_Add (5.0);
   
   Test_Subtract (0.0);
   Test_Subtract (-5.0);
   Test_Subtract (5.0);
   
   Test_Multiply (0.0);
   Test_Multiply (-5.0);
   Test_Multiply (5.0);
   
   Test_Divide (0.0);
   Test_Divide (-5.0);
   Test_Divide (5.0);
   
end Test_Binary_Fixed;
   
