package body Call_Actuals is

   G, H : Integer := 0;

   procedure FI (X, Y : in out Integer) is
   begin
      X := G;
      Y := G + 1;
   end FI;

   procedure FN (X, Y : in out Natural) is
   begin
      X := G;
      Y := G + 1;
   end FN;

   procedure FT (X, Y : in out T) is
   begin
      X := T(G);
      Y := T(G) + 1;
   end FT;

   procedure FNT (X, Y : in out NT) is
   begin
      X := NT(G);
      Y := NT(G) + 1;
   end FNT;

   procedure FS (X, Y : in out S) is
   begin
      X := T(G);
      Y := T(G) + 1;
   end FS;

   procedure Call is
   begin
      FI (G, H);
      FN (G, H);
      FT (T(G), T(H));
      FNT (NT(G), NT(H));
      FS (T(G), T(H));
   end Call;

end Call_Actuals;
