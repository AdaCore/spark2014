package P is

   type T1 is record
      C1 : Boolean;
   end record;

   type T2 is record
      C2 : T1;
   end record;

   protected PO is
      --  All of following routines merely copy Y->X (leaving PO as it was):
      procedure Id0 (X : Boolean; Y : out Boolean) with Depends => (Y => X, PO => PO);
      procedure Id1 (X : Boolean; Y : out Boolean) with Depends => (Y => X, PO => PO);
      procedure Id2 (X : Boolean; Y : out Boolean) with Depends => (Y => X, PO => PO);
      procedure Id3 (X : Boolean; Y : out Boolean) with Depends => (Y => X, PO => PO);
   private
      Pocket1 : T2 := (C2 => (C1 => True));
   end;

   Pocket2 : T2 := (C2 => (C1 => True)) with Part_Of => PO;

end;
