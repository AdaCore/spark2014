with Bad;

package P with SPARK_Mode is

   protected type PT with SPARK_Mode is
      pragma Interrupt_Priority (Bad.Expr.all);
   end;

   PO : PT;

end;
