procedure P is
   type Enum is (A, BC, ABC, A_B_C, ABCD);
   subtype Sub_Enum is Enum range A .. BC;

   type New_Enum is new Enum;
   subtype Sub_New is New_Enum range A .. BC;

begin
   null;
end P;
