package Const is 
   C : constant Integer;
   function Get return Integer with Post => Get'Result = C;
   function Get2 return Integer with Post => Get2'Result = 10_000;
private
   C : constant Integer := 10_000;
   function Get return Integer is (C);
   function Get2 return Integer is (Get);
end Const;
