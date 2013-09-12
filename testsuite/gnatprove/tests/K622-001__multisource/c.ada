package A is pragma SPARK_Mode (On); 
   procedure Foo;
end A;

with B;
package body A is pragma SPARK_Mode (On); 
   procedure Foo is
   begin
      B.Bar;
   end Foo;
end A;

package B is pragma SPARK_Mode (On); 
   procedure Bar;
end B;

package body B is pragma SPARK_Mode (On); 
   procedure Bar is
   begin
      null;
   end Bar;
end B;
