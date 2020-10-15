procedure Init_Wrapper_Simple (B : Boolean) with SPARK_Mode is

   package Nested is
      type Priv is private;
      type Priv2 (D : Integer) is private;
      procedure Init (X : out Priv) with Import;
      procedure Init (X : out Priv2) with Import;
   private
      pragma SPARK_Mode (Off);
      type Priv is new Integer;
      type Priv2 (D : Integer) is null record;
   end Nested;
   use Nested;

   type Empty is null record;

   type T is record
      F : Priv;
      G : Priv2 (5);
      H : Empty;
   end record;

   X : T with Relaxed_Initialization;
   Y : Priv with Relaxed_Initialization;
   Z : Priv2 (4) with Relaxed_Initialization;

begin
   if B then
      pragma Assert (X'Initialized);
      pragma Assert (Y'Initialized);
      pragma Assert (Z'Initialized);
   else
      Init (X.F);
      Init (X.G);
      pragma Assert (X'Initialized);
      Init (Y);
      pragma Assert (Y'Initialized);
      Init (Z);
      pragma Assert (Z'Initialized);
   end if;
end Init_Wrapper_Simple;
