with Remote1; pragma Elaborate_All (Remote1);
with Remote2; pragma Elaborate_All (Remote2);

package P is

   X : Integer := Remote1.Foo;
   Y : Integer := Remote2.Foo;

end;
