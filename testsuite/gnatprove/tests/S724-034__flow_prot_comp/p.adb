package body P is
   protected body PO is

      procedure Id0 (X : Boolean; Y : out Boolean) is
         Tmp : constant Boolean := X;
         --  Copy using a local constant
      begin
         Y := Tmp;
      end;

      procedure Id1 (X : Boolean; Y : out Boolean) is
         Tmp : constant Boolean := Pocket1.C2.C1;
         --  Copy using protected component (with implicit prefix)
      begin
         Pocket1.C2.C1 := X;
         Y := Pocket1.C2.C1;
         Pocket1.C2.C1 := Tmp;
      end;

      procedure Id2 (X : Boolean; Y : out Boolean) is
         Tmp : constant Boolean := PO.Pocket1.C2.C1;
         --  Copy using protected component (with explicit prefix)
      begin
         PO.Pocket1.C2.C1 := X;
         Y := PO.Pocket1.C2.C1;
         PO.Pocket1.C2.C1 := Tmp;
      end;

      procedure Id3 (X : Boolean; Y : out Boolean) is
         Tmp : constant Boolean := Pocket2.C2.C1;
         --  Copy using Part_Of component
      begin
         Pocket2.C2.C1 := X;
         Y := Pocket2.C2.C1;
         Pocket2.C2.C1 := Tmp;
      end;

   end PO;
end;
