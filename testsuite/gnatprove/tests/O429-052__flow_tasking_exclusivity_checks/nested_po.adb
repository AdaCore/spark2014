package body nested_po is

   protected body PT is
      entry Dummy when True is
      begin
         null;
      end;
   end;

   task body TT is
   begin
      Outer_Rec.Inner_Rec.PO.Dummy;
   end;

end;
