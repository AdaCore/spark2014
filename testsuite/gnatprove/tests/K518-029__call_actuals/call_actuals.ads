package Call_Actuals is

   type T is range -20 .. 20;
   type NT is new T range 0 .. 20;
   subtype S is T range 0 .. 20;

   procedure FI (X, Y : in out Integer) with Post => Y = X + 1;
   procedure FN (X, Y : in out Natural) with Post => Y = X + 1;
   procedure FT (X, Y : in out T) with Post => Y = X + 1;
   procedure FNT (X, Y : in out NT) with Post => Y = X + 1;
   procedure FS (X, Y : in out S) with Post => Y = X + 1;

   procedure Call;

end Call_Actuals;
