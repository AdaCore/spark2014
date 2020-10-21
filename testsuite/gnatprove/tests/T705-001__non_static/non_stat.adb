package body Non_Stat is

   protected body PO is
      procedure P (X : Integer) is
         Y : constant Integer := X;
      begin
         pragma Assert (X = Y);
      end P;

   end PO;

end Non_Stat;
