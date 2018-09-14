with Ext;
package P with Initializes => B
is
   protected PO is
   end PO;

   B : Integer := Ext.Var
     with Part_Of => PO;

   package Nested with Initializes => C
   is
      protected Nested_PO is
      end Nested_PO;

      C : Integer := Ext.Var
        with Part_Of => Nested_PO;

   end Nested;
end P;
