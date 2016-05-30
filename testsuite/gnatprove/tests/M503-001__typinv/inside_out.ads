package Inside_Out is

   type T is private;

   procedure Create (X : out T);

   procedure Update (X : in out T);

   function Get (X : T) return Integer;

private

   type T is new Integer with
     Type_Invariant => T /= 0;

   procedure Priv_Create (X : out T);

   procedure Priv_Update (X : in out T);

   function Priv_Get (X : T) return Integer;

end Inside_Out;
