package body Func_Return is

   G : Integer := 0;

   function FI return Integer is
   begin
      return G;
   end FI;

   function FN return Natural is
   begin
      return G;
   end FN;

   function FT return T is
   begin
      return T(G);
   end FT;

   function FNT return NT is
   begin
      return NT(G);
   end FNT;

   function FS return S is
   begin
      return T(G);
   end FS;

   procedure Call is
   begin
      G := FI;
      G := FN;
      G := Integer (FT);
      G := Integer (FNT);
      G := Integer (FS);
   end Call;

end Func_Return;
