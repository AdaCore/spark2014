with Ada.Text_IO; use Ada.Text_IO;

package body PO is

   protected body Foo is
      procedure Bar is
      begin
         pragma Debug (Zoo.Bar);
         pragma Debug (Put_Line ("o<"));
      end Bar;

   end Foo;

   protected body Zoo is
      procedure Bar is
      begin
         Put_Line ("o<");
      end Bar;

   end Zoo;

end PO;
