package A is pragma SPARK_Mode (On);
   procedure Foo (X : in out Integer);
end A;

with B;
package body A is pragma SPARK_Mode (On);
   procedure Foo (X : in out Integer) is
   begin
      B.Bar (X);
      X := X + 1;
   end Foo;
end A;

package B is pragma SPARK_Mode (On);
   procedure Bar (X : in out Integer);
end B;

package body B is pragma SPARK_Mode (On);
   procedure Bar (X : in out Integer) is
   begin
      X := X + 1;
   end Bar;
end B;
