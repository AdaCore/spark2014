package Sax_Symbols is
   type Symbol is private;
   C : constant Symbol;
private
   type Symbol is access all Integer;
   subtype Element is Symbol;
   D : constant Element := null;
   C : constant Symbol := D;
end Sax_Symbols;
