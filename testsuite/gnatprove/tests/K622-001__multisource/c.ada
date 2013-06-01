package A is
   procedure Foo;
end A;

with B;
package body A is
   procedure Foo is
   begin
      B.Bar;
   end Foo;
end A;

package B is
   procedure Bar;
end B;

package body B is
   procedure Bar is
   begin
      null;
   end Bar;
end B;
