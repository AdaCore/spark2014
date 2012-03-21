package body Pack is
   function Query_X2 return T2 is (X2);

   function Query_X1_Bis return Boolean with
     Post => Query_X1_Bis'Result = True;

   function Query_X1_Bis return Boolean is (X1.X);

   function Query_X2_Bis return T2 with
     Post => Query_X2_Bis'Result = 3;

   function Query_X2_Bis return T2 is
   begin
      return X2;
   end Query_X2_Bis;
end Pack;
