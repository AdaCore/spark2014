with Other;
with Other2;

package body P is
   function Fun return Integer is
      Tmp : Integer;
   begin
      Other.Vol_Proc (Tmp);  --  Problem: This makes Fun a Volatile_Function
      return Tmp;
   end Fun;

   function Fun2 return Integer is
      Tmp : Integer;
   begin
      Other2.Vol_Proc (Tmp);  --  Problem: This makes Fun2 a Volatile_Function
      return Tmp;
   end Fun2;
end P;
