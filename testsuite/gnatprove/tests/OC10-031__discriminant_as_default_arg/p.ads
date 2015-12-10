package P is

   protected type PT (D : Integer) is
      procedure Dummy (Arg : Integer := D) with Pre => Arg /= D;
   end;

   PO : PT (0);

end;
